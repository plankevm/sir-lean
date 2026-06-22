Optimized IR:
/// @use-src 0:"Storage2.sol"
object "Storage_12" {
    code {
        {
            /// @src 0:26:166  "contract Storage {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("Storage_12_deployed")
            codecopy(_1, dataoffset("Storage_12_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Storage2.sol"
    object "Storage_12_deployed" {
        code {
            {
                /// @src 0:26:166  "contract Storage {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x2a24ab1f, shr(224, calldataload(0))) { external_fun_store5() }
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
            function external_fun_store5()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_store5()
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
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
            /// @ast-id 11 @src 0:112:164  "function store5() public {..."
            function fun_store5()
            {
                /// @src 0:147:157  "number = 5"
                update_storage_value_offset_uint256_to_uint256(0x00, /** @src 0:156:157  "5" */ 0x05)
            }
        }
        data ".metadata" hex"a264697066735822122063cdb8d37932ac731b01dc445558cd9551bf6e082a61c08a0b1561eed01c96d964736f6c634300081e0033"
    }
}

