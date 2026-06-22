import Mathlib.Data.Nat.Log

import Evm.Maps.AccountMap
import Evm.UInt256
import Evm.State.Substate
import Evm.State.ExecutionEnv
import Evm.Exception
import Evm.Wheels

import Evm.Crypto.EllipticCurves
import Evm.Crypto.RIP160
import Evm.Crypto.BN_ADD
import Evm.Crypto.BN_MUL
import Evm.Crypto.SNARKV
import Evm.Crypto.PointEval

import Evm.FFI.ffi

namespace Evm.Precompiles

def ecRecover
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ := 3000

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let d := env.calldata
    let h := d.readBytes 0 32
    let v := d.readBytes 32 32
    let r := d.readBytes 64 32
    let s := d.readBytes 96 32
    let v' : ℕ := fromByteArrayBigEndian v
    let r' : ℕ := fromByteArrayBigEndian r
    let s' : ℕ := fromByteArrayBigEndian s
    let o :=
      if v' < 27 || 28 < v' || r' = 0 || r' >= secp256k1n || s' = 0 || s' >= secp256k1n then
        .empty
      else
        match ECDSARECOVER h ⟨#[.ofNat v' - 27]⟩ r s with
          | .ok s =>
              ffi.ByteArray.zeroes 12 ++ (ffi.KEC s).extract 12 32
          | .error _ =>
            .empty
    (true, accounts, gas - .ofNat requiredGas, substate, o)

def sha256
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ :=
    let l := env.calldata.size
    let ceil := ( l + 31 ) / 32
    60 + 12 * ceil

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o :=
      match ffi.SHA256 env.calldata with
        | .ok s => s
        | .error _ =>
          .empty
    (true, accounts, gas - .ofNat requiredGas, substate, o)

def ripemd160
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ :=
    let l := env.calldata.size
    let ceil := ( l + 31 ) / 32
    600 + 120 * ceil

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o :=
      match RIP160 env.calldata with
        | .ok s => s
        | .error _ =>
          .empty
    (true, accounts, gas - .ofNat requiredGas, substate, o)

def identity
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ :=
    let l := env.calldata.size
    let ceil := ( l + 31 ) / 32
    15 + 3 * ceil

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o := env.calldata
    (true, accounts, gas - .ofNat requiredGas, substate, o)

def nat_of_slice
  (B: ByteArray)
  (start: ℕ)
  (width: ℕ) : ℕ
:=
  let slice := B.readWithoutPadding start width
  let padding := width - slice.size
  fromByteArrayBigEndian slice <<< (8 * padding)

def expModAux (m : ℕ) (a : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => a % m
  | n@(k + 1) =>
    if n % 2 == 1 then
      expModAux m (a * c % m) (c * c % m) (n / 2)
    else
      expModAux m (a % m)     (c * c % m) (n / 2)

def expMod (m : ℕ) (b : UInt256) (n : ℕ) : ℕ := expModAux m 1 b.toNat n

def modExp
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let data := env.calldata
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  let exp := λ () ↦ nat_of_slice data (96 + base_length) exp_length

  let requiredGas :=
    let multiplication_complexity x y := ((max x y + 7) / 8) ^ 2
    let adjusted_exp_length :=
      if exp_length ≤ 32 && exp () == 0 then
        0
      else
        if exp_length ≤ 32 then
          Nat.log 2 (exp ())
        else
          let length_part := 8 * (exp_length - 32)
          let bits_part :=
            let exp_head := nat_of_slice data (96 + base_length) 32
            if 32 < exp_length ∧ exp_head != 0 then
              Nat.log 2 exp_head
            else
              0
          length_part + bits_part
    let iterations := max adjusted_exp_length 1
    let G_quaddivisor := 3

    max 200 (multiplication_complexity base_length modulus_length * iterations / G_quaddivisor)

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let modulus := nat_of_slice data (96 + base_length + exp_length) modulus_length
    let o : ByteArray :=
      if modulus_length == 0 || modulus == 0 then
        ffi.ByteArray.zeroes ⟨modulus_length⟩
      else
        let base := nat_of_slice data 96 base_length
        let exp := nat_of_slice data (96 + base_length) exp_length
        let expmod_base := BE (expMod modulus (.ofNat base) exp)
        let expmod_zeroes :=
          if modulus_length ≥ expmod_base.size then
            ffi.ByteArray.zeroes ⟨modulus_length - expmod_base.size⟩
          else
            ByteArray.empty
        expmod_zeroes ++ expmod_base
    (true, accounts, gas - .ofNat requiredGas, substate, o)

def ecAdd
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ := 150

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let d := env.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let y := (d.readBytes 64 32, d.readBytes 96 32)
    let o := BN_ADD x.1 x.2 y.1 y.2
    match o with
      | .ok o => (true, accounts, gas - .ofNat requiredGas, substate, o)
      | .error _ =>
        (false, ∅, 0, substate, .empty)

def ecMul
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let requiredGas : ℕ := 6000

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let d := env.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let n := d.readBytes 64 32
    let o := BN_MUL x.1 x.2 n
    match o with
      | .ok o => (true, accounts, gas - .ofNat requiredGas, substate, o)
      | .error _ =>
        (false, ∅, 0, substate, .empty)

def ecPairing
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let d := env.calldata
  let k := d.size / 192
  let requiredGas : ℕ := 34000 * k + 45000

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o := SNARKV d
    match o with
      | .ok o => (true, accounts, gas - .ofNat requiredGas, substate, o)
      | .error _ =>
        (false, ∅, 0, substate, .empty)

def blake2f
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let d := env.calldata
  let requiredGas : ℕ := fromByteArrayBigEndian (d.extract 0 4)

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o := ffi.BLAKE2 d
    match o with
      | .ok o => (true, accounts, gas - .ofNat requiredGas, substate, o)
      | .error _ =>
        (false, ∅, 0, substate, .empty)

def pointEvaluation
  (accounts : AccountMap)
  (gas : UInt64)
  (substate : Substate)
  (env : ExecutionEnv)
    :
  (Bool × AccountMap × UInt64 × Substate × ByteArray)
:=
  let d := env.calldata
  let requiredGas : ℕ := 50000

  if gas.toNat < requiredGas then
    (false, ∅, 0, substate, .empty)
  else
    let o := PointEval d
    match o with
      | .ok o => (true, accounts, gas - .ofNat requiredGas, substate, o)
      | .error _ =>
        (false, ∅, 0, substate, .empty)

end Evm.Precompiles
