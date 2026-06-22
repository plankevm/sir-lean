pragma solidity >=0.8.2 <0.9.0;

interface Storage2Contract {
    function store5() external;
}

contract Storage {

    uint256 number;

    function store(uint256 num) public {
        number = num;
    }

    function retrieve() public view returns (uint256){
        return number;
    }

    function storageDelegateCallTest() public {
        address storage2ContractAddr = address(0x04); // Ensure Storage2Contract is set up at address 4
        Storage2Contract c = Storage2Contract(storage2ContractAddr);
        (bool success, ) = address(c).delegatecall(
            abi.encodeWithSignature("store5()")
        );       
    }

    function storageCallCodeTest() public {
        address storage2ContractAddr = address(0x04); // Ensure Storage2Contract is set up at address 4
        Storage2Contract c = Storage2Contract(storage2ContractAddr);
        (bool success, ) = address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)
            abi.encodeWithSignature("store5()")
        );       
    }

    
}