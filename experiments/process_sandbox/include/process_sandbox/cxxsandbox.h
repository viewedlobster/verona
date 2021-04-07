// Copyright Microsoft and Project Verona Contributors.
// SPDX-License-Identifier: MIT

#pragma once
#include "sandbox.h"
/**
 * The generic sandbox code requires that libraries provide an initialisation
 * function and a dispatcher function, a vtable, and code for storing call
 * frames in memory that allows the dispatcher to invoke them.  In Verona, this
 * will be generated by `veronac`.  This file provides C++ helpers that manage
 * everything using C++ compile-time type information.
 *
 * Correctly using sandboxes from C++ requires sanitising every pointer that
 * you might follow, which C++ can't help with.  This code is therefore
 * mainly useful for testing.
 */

namespace sandbox
{
  /**
   * The argument frame for a sandboxed function.  This contains space for the
   * return value and the arguments.
   */
  template<typename Ret, typename... Args>
  struct argframe
  {
    /**
     * The return value of this function.  If the return value is void, uses
     * char as an unused placeholder.
     */
    std::conditional_t<std::is_void_v<Ret>, char, Ret> ret;
    /**
     * The arguments to the function.
     */
    std::tuple<std::remove_reference_t<Args>...> args;
    // FIXME: This strips references, so we copy arguments, but should probably
    // turn references into pointers.
  };

  /**
   * A wrapper for invoking a function exported from a sandbox.
   */
  template<typename Ret, typename... Args>
  class Function
  {
    /**
     * When constructed with the public constructor, this function uses the
     * private constructor to create a sandboxed function that calls into the
     * child to confirm type signature agreement.  All instances of this
     * template must therefore be allowed to call the private constructor, so
     * are all friends.
     */
    template<typename R, typename... A>
    friend class Function;
    /**
     * The library that exports the function around which this is a wrapper.
     */
    Library& lib;
    /**
     * The correct argument frame type for this specific instantiation.
     */
    using CallFrame = argframe<Ret, Args...>;
    /**
     * The index of this function in the library's vtable.
     */
    int vtable_index;
    /**
     * Designated constructor.  The public constructor both delegates to this
     * and calls it when construction a new temporary sandboxed function to
     * perform type checking.
     */
    Function(Library& l, int idx) : lib(l), vtable_index(idx) {}

  public:
    /**
     * Public constructor.  Called with a sandboxed library as an argument and
     * registers itself as the function in the next vtable slot.  Instances of
     * this class should be created as fields of a structure representing an
     * interface to a sandboxed library, where each exported function field is
     * declared in the same order that it is exported from the library.
     */
    Function(Library& l) : Function(l, l.next_vtable_entry())
    {
#ifndef NDEBUG
      Function<char*, int> get_type(l, 0);
      char* exported = get_type(vtable_index);
      Ret (*fn)(Args...);
      if ((exported == nullptr) || (strcmp(exported, typeid(fn).name()) != 0))
      {
        exit(EXIT_FAILURE);
      }
      lib.free(exported);
#endif
    }
    /**
     * call operator.  Passes the arguments into the sandbox, signals it to
     * invoke the method, and waits for the return value to be propagated.
     */
    Ret operator()(Args... args)
    {
      CallFrame* callframe = lib.alloc<CallFrame>();
      callframe->args = std::forward_as_tuple(args...);
      lib.send(vtable_index, callframe);
      if constexpr (!std::is_void_v<Ret>)
      {
        Ret r = callframe->ret;
        lib.free(callframe);
        return r;
      }
      else
      {
        lib.free(callframe);
      }
    }
  };

  /**
   * Interface for a function exported from a sandbox.  This is used to provide
   * a single set of virtual functions that can invoke all of the specialised
   * versions defined in the templated subclass.
   */
  struct ExportedFunctionBase
  {
    /**
     * Call the function.  The `callframe` parameter is a pointer to an
     * `argframe<Ret, Args...>` corresponding to the return and argument types
     * of the function.
     */
    virtual void operator()(void* callframe) = 0;
    /**
     * Virtual destructor.  This class and its subclasses have trivial
     * destructors, so this is completely unnecessary, but this silences some
     * compiler warnings.
     */
    virtual ~ExportedFunctionBase() {}
    /**
     * Return the type encoding string of the function.  This is used to detect
     * type mismatches between exported and imported functions.
     */
    virtual char* type_encoding() = 0;
  };

  /**
   * Concrete implementation of an exported function.  This template generates
   * the trampoline required to call a function with the specified signature.
   */
  template<typename Ret, typename... Args>
  class ExportedFunction : public ExportedFunctionBase
  {
    /**
     * The type of the structure containing the arguments and the return
     * value for this function.
     */
    using CallFrame = argframe<Ret, Args...>;
    /**
     * A pointer to the function that will be called by this class.
     */
    Ret (*function)(Args...);
    /**
     * The type encoding string for this function.
     */
    char* type_encoding() override
    {
      return strdup(typeid(function).name());
    }
    /**
     * Call the function and, if it returns a non-void type, store the result
     * into the frame.
     */
    void operator()(void* callframe) override
    {
      assert(callframe != nullptr);
      auto frame = (static_cast<CallFrame*>(callframe));
      if constexpr (!std::is_void_v<Ret>)
      {
        frame->ret = std::apply(function, frame->args);
      }
      else
      {
        std::apply(function, frame->args);
      }
    }

  public:
    /**
     * Construct a new sandbox-exported function.  This should be called only by
     * the `export_function` in `ExportedLibrary`, but that calls it indirectly
     * and so we can't sensibly do this via a friend definition.
     */
    ExportedFunction(Ret (*fn)(Args...)) : function(fn) {}
  };

  /**
   * Class wrapping a set of functions that are exported from a library.  This
   * class should never be instantiated directly.  A library that is intended
   * to be used in a sandboxed context should implement a function with the
   * following name and signature:
   *
   * ```
   * extern "C" void sandbox_init(sandbox::ExportedLibrary* library);
   * ```
   *
   * The sandbox runner process will call this function, providing it with a
   * pointer to an instance of this class, during setup.
   */
  class ExportedLibrary
  {
    /**
     * The vtable for this library: map from integers to functions that can be
     * invoked.
     */
  public:
    inline static std::vector<std::unique_ptr<ExportedFunctionBase>> functions;

    static void call(int idx, void* args)
    {
      (*functions[idx])(args);
    }
    /**
     * Returns the type encoding string (in a C++ ABI-specific format) of the
     * function at the specified vtable index.
     */
    static char* type_encoding(int idx)
    {
      return functions.at(idx)->type_encoding();
    }
    /**
     * Export a function to consumers of this sandboxed library.  The function
     * is inserted in the next vtable entry so the order of calls to this
     * method from inside the sandbox must match the order of
     * `Function` objects created for a `Library` that
     * corresponds to the outside of this sandbox.
     */
    template<typename Ret, typename... Args>
    static void export_function(Ret (*fn)(Args...))
    {
      if (
        (functions.size() == 0) &&
        (fn != reinterpret_cast<Ret (*)(Args...)>(type_encoding)))
      {
        export_function(type_encoding);
      }
      functions.emplace_back(new ExportedFunction(fn));
    }
  };

  extern "C" void sandbox_call(int idx, void* args)
  {
    ExportedLibrary::call(idx, args);
  }

  /**
   * Helpers that assist with type deduction for `Function` objects.
   *
   * Nothing in this namespace should be used outside of this library.
   */
  namespace internal
  {
    /**
     * Given the types deduced by `signature`, construct the type of a
     * `Function` that corresponds to the type of the original
     * function.
     */
    template<typename Ret, typename T>
    struct extract_args;
    /**
     * Explicit specialisation.  This is the only version that actually exists,
     * but C++17 doesn't let us declare the generic version with these
     * constraints.
     */
    template<typename Ret, typename... T>
    struct extract_args<Ret, std::tuple<T...>>
    {
      /**
       * The wrapper function type for the exported function type provided by
       * the template arguments.
       */
      using wrapper = Function<Ret, T...>;
    };
  }

  /**
   * Construct a sandboxed function proxy that corresponds to the type
   * signature of the function given in the template parameter.
   *
   * Note that this intentionally does not take the function as an argument.
   * The code outside the sandbox does not need to be linked to the library
   * that implements the function (and, ideally, won't be!).  As such, this
   * function can't ever depend on a concrete definition of the function
   * existing, but can depend on its type signature.  This is intended to be
   * used with `decltype(someFunction)` as an explicit template argument.
   */
  template<typename Fn>
  inline auto make_sandboxed_function(Library& l)
  {
    using sig = internal::signature<Fn>;
    return typename internal::extract_args<
      typename sig::return_type,
      typename sig::argument_type>::wrapper{l};
  }
}
