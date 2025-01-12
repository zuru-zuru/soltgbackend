# Repository with Modified solc and tgnonlin Code  

This repository contains modified versions of `solc` and `tgnonlin` tailored for use with SolTG+.  

## **Acknowledgments**  

This work builds upon the following projects:  
- **solc**: [https://github.com/ethereum/solidity](https://github.com/ethereum/solidity)  
- **tgnonlin**: [https://github.com/BritikovKI/aeval/tree/tg-nonlin](https://github.com/BritikovKI/aeval/tree/tg-nonlin)  

---

## **Dependencies**  

### Instructions to Install Dependencies on Ubuntu-24.04  

1. **Boost**  
   The original tgnonlin repository specifies `libboost-1.75.0` as a dependency.  
   - Tested with:  
     - `libboost-1.83.0` (worked)  
     - `libboost-1.73.0` (did not work)  

   Install `libboost-dev-all` using:  
   ```bash
   sudo apt update
   sudo apt install libboost-dev-all
   ```

2. **GMP** 
    Install `libboost-dev-all` using:  
    ```
    sudo apt update
    sudo apt install libgmp-dev
    ```

3. **Z3 (4.12.1)**
    Build Z3 from source. Navigate to a suitable directory to clone the Z3 repository:
    ```
    sudo apt update
    sudo apt install build-essential python3 cmake
    git clone https://github.com/Z3Prover/z3.git
    cd z3
    git checkout z3-4.12.1
    python scripts/mk_make.py
    cd build
    make -j$(nproc)
    sudo make install
    ```
---

Once all dependencies have been installed

## **Clone repo with submodules**

```
git clone --recursive git@github.com:zuru-zuru/soltgbackend.git
cd soltgbackend
```

## **Building solc**
Run the following from the ```./soltgbackend``` directory 
```
cd solc_new/solidity
mkdir build
cd build 
cmake ../
make solc
```

This will create the binary for solc in ```./solc/solc``` which can then be copied to the deps folder of soltgfrontend.

## **Building tgnonlin**

```tgnonlin``` comes with its own version of Z3. To build Z3 run the following from the ```./soltgbackend``` directory:

```
cd tg_final/aeval
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

This will create ```./tgnonlin``` in the current directory, which may then be copied to the ```soltgfrontend/deps``` folder of SolTG+ (```soltgfrontend```). 