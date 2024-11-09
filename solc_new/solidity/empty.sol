// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MinimalContract {
    // A function that does nothing and simply returns
    uint256 x;
    function doNothing() public {
        // No operations
        uint256 y = x;
        assert(true);
        return;
    }

    function callNothing() public  {
        x += 1;
        // No operations
        doNothing();
        return;
    }
}


contract CallingContract {
    // A function that does nothing and simply returns
    function transactNothing(MinimalContract c) public  {
        // No operations
        c.callNothing();
        return;
    }

    function transactNothing2(MinimalContract c) public  {
        // No operations
        address(c).balance;
        c.doNothing();
        return;
    }
}