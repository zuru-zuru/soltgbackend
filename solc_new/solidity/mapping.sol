// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract SimpleStorage {
    // Mapping from an address to a uint value
    mapping(address => uint) public balances;
    mapping(address => uint) public mamamama;

    // Function to set a value in the mapping
    function setBalance(uint _value) public {
        assert(true);
        balances[msg.sender] = _value;
    }

    // Function to get the balance of a specific address
    function getBalance(address _user) public view returns (uint) {
        assert(true);
        return balances[_user];
    }
}
