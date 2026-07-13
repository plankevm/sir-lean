import Evm
import BytecodeLayer.Semantics.Maps

/-!
# `BytecodeLayer.Hoare.AccountMap` — pure account-map presence bricks

Pure `Evm.AccountMap` facts, zero IR / zero recorder / zero `SelfPresent`: the RBMap
non-emptiness prims (`forM_from_nil` / `all2_nil_false` / `find?_some_ne_empty`) and the
arbitrary-address presence layer (`AccPresent` / `AccMono` + their closure lemmas). The public
names remain in the `BytecodeLayer.Hoare` namespace.

`AccountMap = Batteries.RBMap AccountAddress Account compare`, whose `BEq` runs `RBNode.all₂`
(`Batteries/Data/RBMap/Basic.lean:232`): a `StateT`-over-`Option` walk of the left tree against the
right tree's *stream*. Against the empty (`nil`) right tree the stream is empty, so the first visited
node's `next?` returns `none` and short-circuits the whole walk to `none` — never matching
`some (_, .nil)`. `forM_from_nil` proves exactly this short-circuit; `all2_nil_false` packages it;
`find?_some_ne_empty` is the account-map fact (`find?` hit ⇒ `¬ (m == ∅)`).

No `sorry`/`axiom`/`native_decide`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace BytecodeLayer.Hoare

open Batteries in
/-- The `all₂` `StateT (RBNode.Stream β) Option` walk of `t` against the **empty** stream is `none`
for a non-`nil` `t` (and `some (⟨⟩, .nil)` for `nil`): from the empty initial state, the first node
visited calls `next?` on `.nil` (`= none`) and short-circuits. Proved by structural induction on
`t`, casing the left child (the leftmost-first descent of `RBNode.forM`). -/
theorem forM_from_nil {α β : Type} (R : α → β → Bool) (t : RBNode α) :
    StateT.run (s := (RBNode.Stream.nil : RBNode.Stream β))
      (t.forM (fun a s => do
        let (b, s) ← s.next?
        bif R a b then pure (⟨⟩, s) else none))
    = (match t with
        | .nil => some ((⟨⟩ : PUnit), (RBNode.Stream.nil : RBNode.Stream β))
        | _ => none) := by
  induction t with
  | nil => rfl
  | node c l v r ihl ihr =>
    show (StateT.run (RBNode.forM _ l) RBNode.Stream.nil >>= fun x =>
           StateT.run ((fun a s => _) v) x.2 >>= fun y =>
             StateT.run (RBNode.forM _ r) y.2) = none
    cases l with
    | nil =>
      rw [show StateT.run (RBNode.forM (fun a s => do
              let (b, s) ← s.next?; bif R a b then pure (⟨⟩, s) else none)
              (RBNode.nil : RBNode α)) RBNode.Stream.nil
            = some ((⟨⟩ : PUnit), (RBNode.Stream.nil : RBNode.Stream β)) from ihl]
      rfl
    | node c' l' v' r' => rw [ihl]; rfl

open Batteries in
/-- `RBNode.all₂ R t nil = false` for any non-`nil` `t`: the empty right tree's stream is empty, so
the walk (`forM_from_nil`) short-circuits to `none`, which does not match `some (_, .nil)`. -/
theorem all2_nil_false {α β : Type} (R : α → β → Bool) (t : RBNode α) (hne : t ≠ .nil) :
    RBNode.all₂ R t RBNode.nil = false := by
  unfold RBNode.all₂
  have hrun := forM_from_nil R t
  rw [show (RBNode.nil : RBNode β).toStream = RBNode.Stream.nil from rfl]
  cases t with
  | nil => exact absurd rfl hne
  | node c l v r => rw [hrun]

open Batteries in
/-- **The new account-map fact.** A `find?` hit (`m.find? addr = some acc`) forces `m`'s underlying
tree non-`nil`, and the empty map's tree IS `nil`, so the structural `BEq` (`RBNode.all₂ (·==·)
tree nil`, `all2_nil_false`) is `false`: `¬ (m == ∅)`. Pure account-map fact — does NOT re-supply
`SelfPresent` (it only consumes the `find? = some` witness `SelfPresent` provides). -/
theorem find?_some_ne_empty (m : Evm.AccountMap) (addr : Evm.AccountAddress) (acc : Evm.Account)
    (h : m.find? addr = some acc) : ¬ (m == (∅ : Evm.AccountMap)) = true := by
  intro hbeq
  -- a `find?` hit forces the underlying red-black tree non-`nil` (`find? nil = none`).
  have htree : m.1 ≠ .nil := by
    intro hc
    rw [RBMap.find?, RBMap.findEntry?, RBSet.findP?, hc] at h
    simp [RBNode.find?] at h
  -- `(m == ∅)` IS `RBNode.all₂ (·==·) m.1 nil`, which is `false` for non-`nil` `m.1`.
  have hbeq2 : RBNode.all₂ (· == ·) m.1 RBNode.nil = true := hbeq
  rw [all2_nil_false _ m.1 htree] at hbeq2
  exact Bool.noConfusion hbeq2

/-! ### CALLMONO — account-presence at an *arbitrary* tracked address `a`

`SelfPresent`/`SelfAt` track presence at the frame's *own* self address. To discharge the
`.success` shape of `CallPreservesSelf` we need presence at the **caller's** address tracked across
the *child* drive run, where the running self address is the *callee's* — i.e. presence at an
address `a` that is *not* the running frame's self. We therefore generalise `SelfAt` to an arbitrary
`a` (`AccPresent a`) and prove account-presence monotone across each engine step (`AccMono a`).

The two account framing facts (`Brick A`/`Brick B`) are pure `AccountMap` lemmas; they cover the
SSTORE/TSTORE insert-at-self writes (presence at *any* `a` survives an insert) and the
`SelfPresent ⇒ ≠ ∅` non-emptiness bridge (the `==∅` swap is harmless on a present `a`) at an
arbitrary tracked `a`. -/

/-- Account `a` is present in the map `m`. The arbitrary-address generalisation of `SelfAt` (which
fixes `a := exec.executionEnv.address`). -/
def AccPresent (a : Evm.AccountAddress) (m : Evm.AccountMap) : Prop :=
  ∃ acc : Evm.Account, m.find? a = some acc

/-- Account-presence at `a` is monotone from `m` to `m'`: if `a` is present in `m` it is present in
`m'`. The per-step invariant threaded through the child drive run. -/
def AccMono (a : Evm.AccountAddress) (m m' : Evm.AccountMap) : Prop :=
  AccPresent a m → AccPresent a m'

/-- **Brick A — presence at `a` survives an `insert` at any key.** Case `a = k`: the inserted entry
is read back (`accounts_find?_insert_self`). Case `a ≠ k`: the insert is framed away
(`accounts_find?_insert_of_ne`) and `a`'s old entry survives. This is the SSTORE/TSTORE closer at an
*arbitrary* tracked `a` (the existing self-specific closers insert *at* `a := self`). -/
theorem accounts_find?_insert_mono (m : Evm.AccountMap) (a k : Evm.AccountAddress)
    (v : Evm.Account) (h : AccPresent a m) : AccPresent a (m.insert k v) := by
  obtain ⟨acc, ha⟩ := h
  by_cases hk : a = k
  · subst hk; exact ⟨v, BytecodeLayer.Maps.accounts_find?_insert_self _ _ _⟩
  · exact ⟨acc, by rw [BytecodeLayer.Maps.accounts_find?_insert_of_ne _ _ hk]; exact ha⟩

/-- **Brick B — a present address forces a non-empty map.** If `a` is present in `m` then `m` is not
`∅`. Lifts the `find? = some ⇒ ≠ ∅` tree-nil reduction (the core of `find?_some_ne_empty`) to a
standalone fact ruling out the `==∅` swap branches (precompile `.inr`, `endCall .success`) whenever
the tracked `a` is present. -/
theorem accPresent_ne_empty (a : Evm.AccountAddress) (m : Evm.AccountMap)
    (h : AccPresent a m) : ¬ (m == (∅ : Evm.AccountMap)) = true := by
  obtain ⟨acc, ha⟩ := h
  exact find?_some_ne_empty _ _ _ ha

/-- **`accMono` closer for a verbatim-accounts step.** When `exec'.accounts = exec.accounts`, presence
at `a` transports unchanged (most `.next` arms route through `charge`/`chargeMemExpansion`, which
preserve accounts). -/
theorem accMono_of_accounts_eq (a : Evm.AccountAddress) {m m' : Evm.AccountMap}
    (h : m' = m) : AccMono a m m' := by
  intro hp; rw [h]; exact hp

/-- **Brick B applied — the `==∅` swap is harmless on a present `a`.** For a result of the
`if m == ∅ then m₀ else m` shape, presence at `a` in `m` survives (the `==∅` branch is impossible by
Brick B, so the result is `m`). Used at `endCall .success` and the precompile `.inr` fallback. -/
theorem accMono_emptySwap (a : Evm.AccountAddress) (m m₀ : Evm.AccountMap)
    (h : AccPresent a m) : AccPresent a (if m == (∅ : Evm.AccountMap) then m₀ else m) := by
  rw [if_neg (accPresent_ne_empty a m h)]; exact h

end BytecodeLayer.Hoare
