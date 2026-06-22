pragma solidity ^0.8.30;

interface StorageContract {
    function store(uint256 num) external;
    function retrieve() external returns (uint256);
}

contract CallerContract {

    uint256 number;

    function testStoreAndRetrieveExternal(uint256 v) public {
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        StorageContract c = StorageContract(storageContractAddr);
        c.store(v);
        number = c.retrieve();
    }

}