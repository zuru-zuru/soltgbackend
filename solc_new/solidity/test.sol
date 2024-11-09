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
}


contract SimpleStorage {
    uint256 private storedData1;
    uint256 private storedData2;
    uint256 private storedData3;
    uint256[] public myArray;

    struct User {
        string name;
        uint256 age;
    }

    User x;
    User y;

    constructor() {
        x = User("Alice", 5);
        y = User("Bob", 1);
    }


    // Function to retrieve the stored data
    function get(uint256 x) public returns (uint256) {
        uint256 i = 0;
        // while (i < 10) {
        //     x = 10;
        //     i = i + 1;
        // }
        myArray[5] = 1;
        assert(true);
        if (x + i == 23){
            return x;
        }
        return storedData1;
    }

    function get_set(uint256 x) public returns (uint256) {
        storedData1 = 10;
        return storedData2;
    }

    function set(uint256 z) public returns (uint256) {
        storedData2 = 20;
        x.age = 2;
        return storedData2;
    }
}
