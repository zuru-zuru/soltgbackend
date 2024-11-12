Repository with modified solc and tgnonlin code

## Clone repo with submodules

```
git clone --recursive git@github.com:zuru-zuru/soltgbackend.git
```

## solc

To build solc, make sure Z3 is available during compilation. I built Z3 from source for this. If Z3 is not available or is of an incompatible version, cmake should raise a warning. Once Z3 is available, run:

```
cd solc_new/solidity
mkdir build
cd build 
cmake ../
make solc
```

This will create the binary for solc in ./solc/solc which can then be copied to the deps folder of soltgfrontend.

## tgnonlin

tgnonlin comes with its own version of Z3. To build Z3:

```
cd final_tg/aeval
mkdir build
cd build
cmake ../
cmake --build .  && cmake {path_to_soltgbackend}/tg_final/aeval
```

then run

```
cd tools/nonlin
make tgnonlin
```

This will create ./tgnonlin in the current directory, which may then be copied to the deps folder of soltgfrontend. 