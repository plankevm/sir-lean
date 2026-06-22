pragma solidity ^0.8.30;

contract Storage {

    uint256 number;

    // Intended for testing DELEGATECALL
    function store5() public {
        number = 5;
    }
}