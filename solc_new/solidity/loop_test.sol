// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;



contract MyContract {
    struct User {
        string name;
        uint256 age;
    }

    User x;
    User y;

    constructor() {
        // Initialize the structs in the constructor
        x = User("Alice", 30);
        y = User("Bob", 25);
    }

    function setAgeForX(uint256 newAge) public {
        x.age = newAge; // Now this will work because x is initialized
    }

    function return10() pure private returns (uint256) {
        return 10;
    }

    function get(uint256 x) pure public returns (uint256) {
        x = 10;
        for (uint256 i = 0; i < 10; i++) {
            x = return10();
        }
        // myArray[5] = 1;
        assert(true);
        if (x == 23){
            return x;
        }
        return x;
    }


}


contract SimpleStorage {
    uint256 private storedData1;


    // Function to retrieve the stored data
    function get(uint256 x) public returns (uint256) {
        uint256 i = 0;
        while (i < 10) {
            x = 10;
            i = i + 1;
        }
        // myArray[5] = 1;
        assert(true);
        if (x + i == 23){
            return x;
        }
        return storedData1;
    }


}
