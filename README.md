
Project Verona is a research programming language to explore the concept of
concurrent ownership.  We are providing a new concurrency model that seamlessly
integrates ownership.

This research project is at an early stage and is open sourced to facilitate 
academic collaborations.  We are keen to engage in research collaborations on
this project, please do reach out to discuss this.

The project is not ready to be used outside of research, and is under going a massive refactoring.
The previous version can be found in the `old_version` branch.

## Building and running

Making sure that you have a sufficiently new version of `clang`, build the verona compiler using:
```
mkdir build && cd build
cmake -GNinja .. -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=Debug
ninja install
```

To try out your steaming hot, newly built verona compiler, run
```
./dist/verona/verona build -dw <your file>.verona
```

## [FAQ](docs/faq.md)
