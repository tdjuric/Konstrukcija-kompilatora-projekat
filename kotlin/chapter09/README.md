
```bash
clang++ -Xlinker --export-dynamic -g main.cpp `llvm-config --cxxflags --ldflags --system-libs --libs core orcjit native` -O3 -o main
./main <function.rs
./main <loop.rs
```
