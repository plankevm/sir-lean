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

    function testStaticRetrieve() public returns (uint256) {
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        (bool success, bytes memory data) = storageContractAddr.staticcall(
            abi.encodeWithSignature("retrieve()")
        );
        number = abi.decode(data, (uint256));
    }

    function testStaticStore(uint256 value) public returns (uint256) { // Should raise a .StaticModeViolation
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        (bool success, bytes memory data) = storageContractAddr.staticcall(
            abi.encodeWithSignature("store(uint256)", value)
        );
        number = abi.decode(data, (uint256));
    }


}