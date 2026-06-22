Optimized IR:
/// @use-src 0:"Caller.sol"
object "CallerContract_47" {
    code {
        {
            /// @src 0:151:488  "contract CallerContract {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("CallerContract_47_deployed")
            codecopy(_1, dataoffset("CallerContract_47_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Caller.sol"
    object "CallerContract_47_deployed" {
        code {
            {
                /// @src 0:151:488  "contract CallerContract {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x5ec1cee6, shr(224, calldataload(0)))
                    {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
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
            function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
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
            function abi_decode_fromMemory(headStart, dataEnd)
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
            function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
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
            /// @ast-id 46 @src 0:203:485  "function testStoreAndRetrieveExternal(uint256 v) public {..."
            function fun_testStoreAndRetrieveExternal(var_v)
            {
                /// @src 0:437:447  "c.store(v)"
                let _1 := extcodesize(/** @src 0:151:488  "contract CallerContract {..." */ 2)
                /// @src 0:437:447  "c.store(v)"
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 := /** @src 0:151:488  "contract CallerContract {..." */ mload(64)
                /// @src 0:437:447  "c.store(v)"
                mstore(_2, /** @src 0:151:488  "contract CallerContract {..." */ shl(224, 0x6057361d))
                /// @src 0:437:447  "c.store(v)"
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4, /** @src 0:151:488  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                /// @src 0:466:478  "c.retrieve()"
                let _7 := /** @src 0:151:488  "contract CallerContract {..." */ mload(64)
                /// @src 0:466:478  "c.retrieve()"
                mstore(_7, /** @src 0:151:488  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:466:478  "c.retrieve()"
                let _8 := add(_7, /** @src 0:437:447  "c.store(v)" */ 4)
                /// @src 0:466:478  "c.retrieve()"
                let _9 := gas()
                let _10 := call(_9, /** @src 0:151:488  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:466:478  "c.retrieve()" */ _7, sub(/** @src 0:151:488  "contract CallerContract {..." */ _8, /** @src 0:466:478  "c.retrieve()" */ _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                /// @src 0:457:478  "number = c.retrieve()"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:457:478  "number = c.retrieve()" */ expr)
            }
        }
        data ".metadata" hex"a26469706673582212205a3789c805189821227f43912a5ea5141cb30628cec3c7488d840ad92222a35964736f6c634300081e0033"
    }
}

Optimized IR:

