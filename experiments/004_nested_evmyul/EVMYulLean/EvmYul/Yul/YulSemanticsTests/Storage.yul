Optimized IR:
/// @use-src 0:"Storage.sol"
object "Storage_88" {
    code {
        {
            /// @src 0:97:1065  "contract Storage {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("Storage_88_deployed")
            codecopy(_1, dataoffset("Storage_88_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Storage.sol"
    object "Storage_88_deployed" {
        code {
            {
                /// @src 0:97:1065  "contract Storage {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x2e64cec1 { external_fun_retrieve() }
                    case 0x6057361d { external_fun_store() }
                    case 0xd54d0506 {
                        external_fun_storageCallCodeTest()
                    }
                    case 0xdd15ce8e {
                        external_fun_storageDelegateCallTest()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function external_fun_retrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_retrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            function external_fun_store()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_store(_1)
                return(0, 0)
            }
            function external_fun_storageCallCodeTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageCallCodeTest()
                return(0, 0)
            }
            function external_fun_storageDelegateCallTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageDelegateCallTest()
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            /// @ast-id 25 @src 0:212:291  "function retrieve() public view returns (uint256){..."
            function fun_retrieve() -> var
            {
                /// @src 0:271:284  "return number"
                var := /** @src 0:97:1065  "contract Storage {..." */ sload(/** @src 0:278:284  "number" */ 0x00)
            }
            /// @src 0:97:1065  "contract Storage {..."
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            /// @ast-id 17 @src 0:142:206  "function store(uint256 num) public {..."
            function fun_store(var_num)
            {
                /// @src 0:187:199  "number = num"
                update_storage_value_offset_uint256_to_uint256(0x00, var_num)
            }
            /// @src 0:97:1065  "contract Storage {..."
            function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            /// @ast-id 87 @src 0:643:1057  "function storageCallCodeTest() public {..."
            function fun_storageCallCodeTest()
            {
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                let expr_mpos := /** @src 0:97:1065  "contract Storage {..." */ mload(64)
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                let _1 := add(expr_mpos, 0x20)
                mstore(_1, shl(224, 0x2a24ab1f))
                _1 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_1, expr_mpos), /** @src 0:97:1065  "contract Storage {..." */ not(31)))
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                finalize_allocation(expr_mpos, sub(_1, expr_mpos))
                /// @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..."
                let _2 := mload(expr_mpos)
                let _3 := gas()
                pop(delegatecall(_3, /** @src 0:97:1065  "contract Storage {..." */ 4, /** @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..." */ add(expr_mpos, /** @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")" */ 0x20), /** @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..." */ _2, 0, 0))
                pop(extract_returndata())
            }
            /// @ast-id 56 @src 0:297:637  "function storageDelegateCallTest() public {..."
            function fun_storageDelegateCallTest()
            {
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                let expr_52_mpos := /** @src 0:97:1065  "contract Storage {..." */ mload(64)
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                let _1 := add(expr_52_mpos, 0x20)
                mstore(_1, /** @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")" */ shl(224, 0x2a24ab1f))
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                _1 := add(expr_52_mpos, 36)
                mstore(expr_52_mpos, add(sub(_1, expr_52_mpos), /** @src 0:97:1065  "contract Storage {..." */ not(31)))
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                finalize_allocation(expr_52_mpos, sub(_1, expr_52_mpos))
                /// @src 0:541:623  "address(c).delegatecall(..."
                let _2 := mload(expr_52_mpos)
                let _3 := gas()
                pop(delegatecall(_3, /** @src 0:97:1065  "contract Storage {..." */ 4, /** @src 0:541:623  "address(c).delegatecall(..." */ add(expr_52_mpos, /** @src 0:578:613  "abi.encodeWithSignature(\"store5()\")" */ 0x20), /** @src 0:541:623  "address(c).delegatecall(..." */ _2, 0, 0))
                pop(extract_returndata())
            }
        }
        data ".metadata" hex"a2646970667358221220960c90ddc77bdca69249506d3086cedee34ff2ced8c968d61928a12d4bb5c0d164736f6c634300081e0033"
    }
}

Optimized IR:

