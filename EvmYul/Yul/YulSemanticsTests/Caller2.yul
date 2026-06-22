Optimized IR:
/// @use-src 0:"Caller2.sol"
object "CallerContract_120" {
    code {
        {
            /// @src 0:151:1255  "contract CallerContract {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("CallerContract_120_deployed")
            codecopy(_1, dataoffset("CallerContract_120_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Caller2.sol"
    object "CallerContract_120_deployed" {
        code {
            {
                /// @src 0:151:1255  "contract CallerContract {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x37cbaee8 {
                        external_fun_testStaticStore()
                    }
                    case 0x5ec1cee6 {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                    case 0x8b1218f9 {
                        external_fun_testStaticRetrieve()
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
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function external_fun_testStaticStore()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_testStaticStore(_1)
                let memPos := mload(64)
                let _2 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_2, memPos))
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
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function external_fun_testStaticRetrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_testStaticRetrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
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
            /// @ast-id 119 @src 0:844:1251  "function testStaticStore(uint256 value) public returns (uint256) { // Should raise a .StaticModeViolation..."
            function fun_testStaticStore(var_value) -> var
            {
                /// @src 0:900:907  "uint256"
                var := /** @src 0:151:1255  "contract CallerContract {..." */ 0
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                let expr_105_mpos := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                let _1 := 0x20
                let _2 := add(expr_105_mpos, _1)
                mstore(_2, shl(224, 0x6057361d))
                _2 := add(expr_105_mpos, 36)
                let _3 := abi_encode_uint256(_2, var_value)
                mstore(expr_105_mpos, add(sub(_3, expr_105_mpos), /** @src 0:151:1255  "contract CallerContract {..." */ not(31)))
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                finalize_allocation(expr_105_mpos, sub(_3, expr_105_mpos))
                /// @src 0:1096:1198  "storageContractAddr.staticcall(..."
                let _4 := mload(expr_105_mpos)
                let _5 := gas()
                pop(staticcall(_5, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:1096:1198  "storageContractAddr.staticcall(..." */ add(expr_105_mpos, _1), _4, 0, 0))
                let expr_106_component_2_mpos := extract_returndata()
                /// @src 0:151:1255  "contract CallerContract {..."
                let _6 := mload(/** @src 0:1217:1244  "abi.decode(data, (uint256))" */ expr_106_component_2_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_106_component_2_mpos, _1), add(add(expr_106_component_2_mpos, /** @src 0:151:1255  "contract CallerContract {..." */ _6), /** @src 0:1217:1244  "abi.decode(data, (uint256))" */ _1))
                /// @src 0:1208:1244  "number = abi.decode(data, (uint256))"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:1096:1198  "storageContractAddr.staticcall(..." */ 0, /** @src 0:1208:1244  "number = abi.decode(data, (uint256))" */ expr)
            }
            /// @src 0:151:1255  "contract CallerContract {..."
            function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            /// @ast-id 46 @src 0:203:485  "function testStoreAndRetrieveExternal(uint256 v) public {..."
            function fun_testStoreAndRetrieveExternal(var_v)
            {
                /// @src 0:437:447  "c.store(v)"
                let _1 := extcodesize(/** @src 0:151:1255  "contract CallerContract {..." */ 2)
                /// @src 0:437:447  "c.store(v)"
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:437:447  "c.store(v)"
                mstore(_2, /** @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)" */ shl(224, 0x6057361d))
                /// @src 0:437:447  "c.store(v)"
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                /// @src 0:466:478  "c.retrieve()"
                let _7 := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:466:478  "c.retrieve()"
                mstore(_7, /** @src 0:151:1255  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:466:478  "c.retrieve()"
                let _8 := add(_7, /** @src 0:437:447  "c.store(v)" */ 4)
                /// @src 0:466:478  "c.retrieve()"
                let _9 := gas()
                let _10 := call(_9, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:466:478  "c.retrieve()" */ _7, sub(/** @src 0:151:1255  "contract CallerContract {..." */ _8, /** @src 0:466:478  "c.retrieve()" */ _7), _7, 32)
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
            /// @ast-id 81 @src 0:491:838  "function testStaticRetrieve() public returns (uint256) {..."
            function fun_testStaticRetrieve() -> var_
            {
                /// @src 0:537:544  "uint256"
                var_ := /** @src 0:151:1255  "contract CallerContract {..." */ 0
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                let expr_mpos := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                let _1 := 0x20
                let _2 := add(expr_mpos, _1)
                mstore(_2, /** @src 0:151:1255  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                _2 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_2, expr_mpos), /** @src 0:151:1255  "contract CallerContract {..." */ not(31)))
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                finalize_allocation(expr_mpos, sub(_2, expr_mpos))
                /// @src 0:694:785  "storageContractAddr.staticcall(..."
                let _3 := mload(expr_mpos)
                let _4 := gas()
                pop(staticcall(_4, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:694:785  "storageContractAddr.staticcall(..." */ add(expr_mpos, _1), _3, 0, 0))
                let expr_component_mpos := extract_returndata()
                /// @src 0:151:1255  "contract CallerContract {..."
                let _5 := mload(/** @src 0:804:831  "abi.decode(data, (uint256))" */ expr_component_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_component_mpos, _1), add(add(expr_component_mpos, /** @src 0:151:1255  "contract CallerContract {..." */ _5), /** @src 0:804:831  "abi.decode(data, (uint256))" */ _1))
                /// @src 0:795:831  "number = abi.decode(data, (uint256))"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:694:785  "storageContractAddr.staticcall(..." */ 0, /** @src 0:795:831  "number = abi.decode(data, (uint256))" */ expr)
            }
        }
        data ".metadata" hex"a2646970667358221220e24661e83e0bb60c2412c749f45703a27bf49c055bcde51c906f337d26b3685564736f6c634300081e0033"
    }
}

Optimized IR:

