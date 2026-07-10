import LirLean.Spec.Semantics
import LirLean.Spec.Lowering
import LirLean.Materialise.MaterialiseGas
import LirLean.Materialise.DefsSound
import LirLean.Decode.DecodeLower

namespace Lir.V2

open Evm

-- Local readiness for executing one statement at a concrete state. `.gas` is
-- always definable from the gas oracle; calls require only the source operands,
-- while their effects are supplied by the call/create streams.
def StmtDefinableG (st : IRState) : Stmt → Prop
  | .assign _ e => e = .gas ∨ ∃ w, evalExpr st 0 e = some w
  | .sstore key value => (∃ kw, st.locals key = some kw) ∧ (∃ vw, st.locals value = some vw)
  | .call cs => (∃ cw, st.locals cs.callee = some cw) ∧ (∃ gw, st.locals cs.gasFwd = some gw)
  | .create cs =>
      (∃ valueW, st.locals cs.value = some valueW)
      ∧ (∃ initOffW, st.locals cs.initOffset = some initOffW)
      ∧ (∃ initSizeW, st.locals cs.initSize = some initSizeW)
      ∧ (∃ saltW, st.locals cs.salt = some saltW)

structure RunDefinableG (prog : Program) : Prop where
  stmts : ∀ (st st' : IRState) (T T' : GasOracle) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (pc : Nat) (s : Stmt),
    blockAt prog L = some b → b.stmts[pc]? = some s →
    RunStmts prog st T C D (b.stmts.take pc) st' T' C' D' →
    StmtDefinableG st' s
  ret_def : ∀ (st st' : IRState) (T T' : GasOracle) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    RunStmts prog st T C D b.stmts st' T' C' D' →
    ∃ w, st'.locals t = some w
  branch_def : ∀ (st st' : IRState) (T T' : GasOracle) (C C' : CallStream) (D D' : CreateStream)
      (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    RunStmts prog st T C D b.stmts st' T' C' D' →
    ∃ cw, st'.locals cond = some cw

def DefsConsistent (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat), blockAt prog L = some b →
    (∀ (t : Tmp) (e : Expr), b.stmts[pc]? = some (.assign t e) →
      defsOf prog t = some (match e with
        | .gas => .slot (slotOf t)
        | .sload _ => .slot (slotOf t)
        | e' => locOfExpr e'))
    ∧ (∀ (cs : CallSpec) (t : Tmp), b.stmts[pc]? = some (.call cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))
    ∧ (∀ (cs : CreateSpec) (t : Tmp), b.stmts[pc]? = some (.create cs) → cs.resultTmp = some t →
      defsOf prog t = some (.slot (slotOf t)))

def ReadsOf (prog : Program) (t t' : Tmp) : Prop :=
  ∃ e', rematOf prog t' = some e' ∧ usesInExpr t e' ≠ 0

def invalStep (prog : Program) (I : Tmp → Prop) : Stmt → (Tmp → Prop)
  | .assign t e => fun t' =>
      if t' = t then usesInExpr t e ≠ 0 else (I t' ∨ ReadsOf prog t t')
  | .sstore _ _ => I
  | .call cs =>
      match cs.resultTmp with
      | some t => fun t' => if t' = t then False else (I t' ∨ ReadsOf prog t t')
      | none => I
  | .create cs =>
      match cs.resultTmp with
      | some t => fun t' => if t' = t then False else (I t' ∨ ReadsOf prog t t')
      | none => I

def DefsSoundS (prog : Program) (I : Tmp → Prop) (st : IRState) : Prop :=
  ∀ (t : Tmp) (e : Expr) (w : Word),
    rematOf prog t = some e → ¬ Lir.NonRecomputable prog t → ¬ I t →
    st.locals t = some w → some w = evalExpr st 0 e

theorem defsSoundS_empty_iff (prog : Program) (st : IRState) :
    DefsSoundS prog (fun _ => False) st ↔ Lir.DefsSound prog st :=
  ⟨fun h t e w hd hn hl => h t e w hd hn not_false hl,
   fun h t e w hd hn _ hl => h t e w hd hn hl⟩

def StepScopedS (prog : Program) : Stmt → Prop
  | .assign t e =>
      (e ≠ .gas → (∀ key, e ≠ .sload key) → rematOf prog t = some e)
      ∧ (e = .gas → Lir.isGasDef prog t)
      ∧ (∀ key, e = .sload key → Lir.isSloadDef prog t)
  | .sstore _ _ =>
      ∀ (t₀ : Tmp) (e₀ : Expr), rematOf prog t₀ = some e₀ → ∀ key, e₀ ≠ .sload key
  | .call cs => ∀ t, cs.resultTmp = some t → Lir.isCallResult prog t
  | .create _ => True

def RevalidatesPerBlock (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block), blockAt prog L = some b →
    ∀ t', ¬ (b.stmts.foldl (invalStep prog) (fun _ => False)) t'

def readsStmt : Stmt → Tmp → Prop
  | .assign _ e, t => usesInExpr t e ≠ 0
  | .sstore key value, t => t = key ∨ t = value
  | .call cs, t => t = cs.callee ∨ t = cs.gasFwd
  | .create cs, t =>
      t = cs.value ∨ t = cs.initOffset ∨ t = cs.initSize ∨ t = cs.salt

inductive RematClosureFree (prog : Program) (I : Tmp → Prop) : Expr → Prop where
  | imm (w) : RematClosureFree prog I (.imm w)
  | gas : RematClosureFree prog I .gas
  | sload (k) : RematClosureFree prog I (.sload k)
  | tmp (t) (hI : ¬ I t)
      (hrem : ∀ e', allocate prog t = some (.remat e') → RematClosureFree prog I e') :
      RematClosureFree prog I (.tmp t)
  | add (a b) (ha : RematClosureFree prog I (.tmp a))
      (hb : RematClosureFree prog I (.tmp b)) :
      RematClosureFree prog I (.add a b)
  | lt (a b) (ha : RematClosureFree prog I (.tmp a))
      (hb : RematClosureFree prog I (.tmp b)) :
      RematClosureFree prog I (.lt a b)

theorem RematClosureFree.tmp_inv {prog : Program} {I : Tmp → Prop} {t : Tmp}
    (h : RematClosureFree prog I (.tmp t)) :
    ¬ I t ∧ ∀ e', allocate prog t = some (.remat e') → RematClosureFree prog I e' := by
  cases h with | tmp _ hI hrem => exact ⟨hI, hrem⟩

theorem RematClosureFree.add_inv {prog : Program} {I : Tmp → Prop} {a b : Tmp}
    (h : RematClosureFree prog I (.add a b)) :
    RematClosureFree prog I (.tmp a) ∧ RematClosureFree prog I (.tmp b) := by
  cases h with | add _ _ ha hb => exact ⟨ha, hb⟩

theorem RematClosureFree.lt_inv {prog : Program} {I : Tmp → Prop} {a b : Tmp}
    (h : RematClosureFree prog I (.lt a b)) :
    RematClosureFree prog I (.tmp a) ∧ RematClosureFree prog I (.tmp b) := by
  cases h with | lt _ _ ha hb => exact ⟨ha, hb⟩

theorem RematClosureFree.mono {prog : Program} {I J : Tmp → Prop} {e : Expr}
    (hsub : ∀ t, J t → I t) (h : RematClosureFree prog I e) :
    RematClosureFree prog J e := by
  induction h with
  | imm w => exact .imm w
  | gas => exact .gas
  | sload k => exact .sload k
  | tmp t hI hrem ih =>
      exact .tmp t (fun hJ => hI (hsub t hJ)) (fun e' he' => ih e' he')
  | add a b _ _ iha ihb => exact .add a b iha ihb
  | lt a b _ _ iha ihb => exact .lt a b iha ihb

def ScopedUses (prog : Program) : Prop :=
  ∀ (L : Label) (b : Block) (pc : Nat) (s : Stmt),
    blockAt prog L = some b → b.stmts[pc]? = some s →
    ∀ t, readsStmt s t →
      RematClosureFree prog
        ((b.stmts.take pc).foldl (invalStep prog) (fun _ => False)) (.tmp t)

structure CFGClosed (prog : Program) : Prop where
  entry_present : ∃ b, blockAt prog prog.entry = some b
  jump_closed : ∀ (L : Label) (b : Block) (dst : Label),
    blockAt prog L = some b → b.term = .jump dst →
    (∃ b', blockAt prog dst = some b') ∧ dst.idx < prog.blocks.size
  branch_closed : ∀ (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    ((∃ b', blockAt prog thenL = some b') ∧ thenL.idx < prog.blocks.size)
    ∧ ((∃ b', blockAt prog elseL = some b') ∧ elseL.idx < prog.blocks.size)

def DefEnvOrdered (prog : Program) : Prop :=
  ∀ (i : Nat) (t : Tmp) (e : Expr),
    (defEnv prog)[i]? = some (t, Loc.remat e) →
    ∀ t' : Tmp, usesInExpr t' e ≠ 0 →
      ∃ j, j < i ∧ ∃ loc : Loc, (defEnv prog)[j]? = some (t', loc)

theorem defEnv_entry_eq_allocate (prog : Program)
    (hdc : DefsConsistent prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    allocate prog t = some loc := by
  rw [defEnv] at hmem
  obtain ⟨b, hbmem, hbmap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨s, hsmem, hsmap⟩ := List.mem_filterMap.mp hbmap
  obtain ⟨i, hi, hbget⟩ := List.mem_iff_getElem.mp hbmem
  obtain ⟨j, hj, hsget⟩ := List.mem_iff_getElem.mp hsmem
  have hblockAt : blockAt prog ⟨i⟩ = some b := by
    show prog.blocks[i]? = some b
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hbget]
  have hstmt : b.stmts[j]? = some s := by
    rw [List.getElem?_eq_getElem hj, hsget]
  cases s with
  | assign t' e =>
    cases e with
    | gas =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' .gas hstmt
    | sload k =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.sload k) hstmt
    | imm w =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.imm w) hstmt
    | tmp t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.tmp t'') hstmt
    | add a c =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.add a c) hstmt
    | lt a c =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).1 t' (.lt a c) hstmt
  | sstore _ _ => simp at hsmap
  | call cs =>
    obtain ⟨callee, gasFwd, rt⟩ := cs
    cases rt with
    | none => simp at hsmap
    | some t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).2.1 ⟨callee, gasFwd, some t''⟩ t'' hstmt rfl
  | create cs =>
    obtain ⟨value, initOffset, initSize, salt, rt⟩ := cs
    cases rt with
    | none => simp at hsmap
    | some t'' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hsmap
      obtain ⟨ht, hloc⟩ := hsmap; subst ht; subst hloc
      exact (hdc ⟨i⟩ b j hblockAt).2.2 ⟨value, initOffset, initSize, salt, some t''⟩ t'' hstmt rfl

theorem matCache_last_eq_first (prog : Program)
    (hdc : DefsConsistent prog)
    {t : Tmp} {loc₁ loc₂ : Loc}
    (h₁ : (t, loc₁) ∈ defEnv prog) (h₂ : (t, loc₂) ∈ defEnv prog) :
    loc₁ = loc₂ :=
  Option.some.inj
    ((defEnv_entry_eq_allocate prog hdc h₁).symm.trans
      (defEnv_entry_eq_allocate prog hdc h₂))

theorem findIdx_le_of_getElem? {α : Type _} {p : α → Bool} :
    ∀ {l : List α} {j : Nat} {x : α}, l[j]? = some x → p x = true → l.findIdx p ≤ j
  | [], _, _, hj, _ => by simp at hj
  | a :: as, 0, x, hj, hx => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj; rw [List.findIdx_cons, hx, cond_true]
  | a :: as, j + 1, x, hj, hx => by
      simp only [List.getElem?_cons_succ] at hj
      rw [List.findIdx_cons]
      cases hpa : p a with
      | true => rw [cond_true]; exact Nat.zero_le _
      | false => rw [cond_false]; exact Nat.succ_le_succ (findIdx_le_of_getElem? hj hx)

theorem defEnv_operand_findIdx_lt {prog : Program} (h : DefEnvOrdered prog)
    {t t' : Tmp} {e : Expr}
    (hget : (defEnv prog)[(defEnv prog).findIdx (fun p => p.1 == t)]? = some (t, Loc.remat e))
    (hu : usesInExpr t' e ≠ 0) :
    (defEnv prog).findIdx (fun p => p.1 == t')
      < (defEnv prog).findIdx (fun p => p.1 == t) := by
  obtain ⟨j, hji, loc', hj⟩ := h _ t e hget t' hu
  have hle : (defEnv prog).findIdx (fun p => p.1 == t') ≤ j :=
    findIdx_le_of_getElem? hj (by simp)
  omega

def matInit : Tmp → List UInt8 := fun _ => emitImm 0

@[simp] theorem matCache_eq_matFold (prog : Program) :
    matCache prog = matFold matInit (defEnv prog) := rfl

theorem matExpr_congr {c c' : Tmp → List UInt8} {e : Expr}
    (h : ∀ t, usesInExpr t e ≠ 0 → c t = c' t) : matExpr c e = matExpr c' e := by
  cases e with
  | imm w => rfl
  | gas => rfl
  | tmp t => simp only [matExpr_tmp]; exact h t (by simp [usesInExpr])
  | add a b =>
      simp only [matExpr_add]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | lt a b =>
      simp only [matExpr_lt]
      rw [h a (by simp [usesInExpr]), h b (by simp [usesInExpr])]
  | sload k => simp only [matExpr_sload]; rw [h k (by simp [usesInExpr])]

theorem matFold_notMem {t : Tmp} :
    ∀ (l : List (Tmp × Loc)) (c : Tmp → List UInt8),
      t ∉ l.map Prod.fst → matFold c l t = c t
  | [], _, _ => rfl
  | p :: l, c, h => by
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [matFold_cons, matFold_notMem l (matStep c p) h.2]
      exact Function.update_of_ne h.1 _ _

theorem matFold_split (c : Tmp → List UInt8) (t : Tmp) :
    ∀ (l : List (Tmp × Loc)),
      (t ∉ l.map Prod.fst ∧ matFold c l t = c t) ∨
      (∃ pre loc post, l = pre ++ (t, loc) :: post ∧ t ∉ post.map Prod.fst ∧
         matFold c l t = matLoc (matFold c pre) loc) := by
  intro l
  induction l using List.reverseRecOn with
  | nil => exact Or.inl ⟨by simp, rfl⟩
  | append_singleton l x ih =>
      have hval : matFold c (l ++ [x]) t
          = if t = x.1 then matLoc (matFold c l) x.2 else matFold c l t := by
        have hfold : matFold c (l ++ [x]) = matStep (matFold c l) x := by
          simp only [matFold, List.foldl_append]; rfl
        rw [hfold]; simp only [matStep, Function.update_apply]
      by_cases hx : t = x.1
      · refine Or.inr ⟨l, x.2, [], ?_, by simp, ?_⟩
        · have hxe : x = (t, x.2) := by rw [hx]
          rw [hxe]
        · rw [hval, if_pos hx]
      · cases ih with
        | inl h =>
            refine Or.inl ⟨?_, ?_⟩
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨h.1, hx⟩
            · rw [hval, if_neg hx]; exact h.2
        | inr h =>
            obtain ⟨pre, loc, post, heq, hpost, hvv⟩ := h
            refine Or.inr ⟨pre, loc, post ++ [x], ?_, ?_, ?_⟩
            · rw [heq, List.append_assoc, List.cons_append]
            · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
                List.mem_singleton, not_or]
              exact ⟨hpost, hx⟩
            · rw [hval, if_neg hx]; exact hvv

theorem defEnv_findIdx_entry (prog : Program) (hdc : DefsConsistent prog)
    {t' : Tmp} {loc : Loc} (hmem : (t', loc) ∈ defEnv prog) :
    (defEnv prog)[(defEnv prog).findIdx (fun p => p.1 == t')]? = some (t', loc) := by
  have hd : defsOf prog t' = some loc := defEnv_entry_eq_allocate prog hdc hmem
  rw [defsOf_eq_defEnv_find, List.find?_eq_getElem?_findIdx, Option.map_eq_some_iff] at hd
  obtain ⟨⟨tt, locc⟩, hget, hsnd⟩ := hd
  have htt : tt = t' := by
    have := List.findIdx_of_getElem?_eq_some hget; simpa using this
  subst htt
  have hll : locc = loc := hsnd
  rw [hget, hll]

theorem operand_mem_take {prog : Program} (hord : DefEnvOrdered prog)
    {i : Nat} {t' t'' : Tmp} {e : Expr}
    (hget : (defEnv prog)[i]? = some (t', Loc.remat e)) (hu : usesInExpr t'' e ≠ 0) :
    t'' ∈ ((defEnv prog).take i).map Prod.fst := by
  obtain ⟨j, hji, locj, hj⟩ := hord i t' e hget t'' hu
  have hjt : ((defEnv prog).take i)[j]? = some (t'', locj) := by
    rw [List.getElem?_take, if_pos hji]; exact hj
  exact List.mem_map_of_mem (List.mem_of_getElem? hjt)

theorem matFold_take_eq_matCache (prog : Program)
    (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog) :
    ∀ (t' : Tmp) (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
      matFold matInit ((defEnv prog).take p) t' = matCache prog t' := by
  have key : ∀ (n : Nat) (t' : Tmp),
      (defEnv prog).findIdx (fun p => p.1 == t') = n →
      ∀ (p : Nat), t' ∈ ((defEnv prog).take p).map Prod.fst →
        matFold matInit ((defEnv prog).take p) t' = matCache prog t' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t' hn p hmem
      have hmemFull : t' ∈ (defEnv prog).map Prod.fst := by
        obtain ⟨y, hy, hy2⟩ := List.mem_map.mp hmem
        exact List.mem_map.mpr ⟨y, List.take_subset p _ hy, hy2⟩
      rcases matFold_split matInit t' ((defEnv prog).take p) with hA | hA
      · exact absurd hmem hA.1
      obtain ⟨preA, locA, postA, hsplitA, _hpostA, hvalA⟩ := hA
      rcases matFold_split matInit t' (defEnv prog) with hB | hB
      · exact absurd hmemFull hB.1
      obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
      have hmemA : (t', locA) ∈ defEnv prog :=
        List.take_subset p _ (by rw [hsplitA]; simp)
      have hmemB : (t', locB) ∈ defEnv prog := by rw [hsplitB]; simp
      have hll : locA = locB := matCache_last_eq_first prog hdc hmemA hmemB
      rw [hvalA, matCache_eq_matFold, hvalB, ← hll]
      have hpreA : preA = (defEnv prog).take preA.length := by
        have h1 : preA <+: (defEnv prog).take p := by
          rw [hsplitA]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp (h1.trans (List.take_prefix p _))
      have hpreB : preB = (defEnv prog).take preB.length := by
        have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
        exact List.prefix_iff_eq_take.mp h1
      have hlenA : preA.length < p := by
        have hlen : ((defEnv prog).take p).length ≤ p := by
          rw [List.length_take]; exact Nat.min_le_left _ _
        rw [hsplitA] at hlen
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have hgetA : (defEnv prog)[preA.length]? = some (t', locA) := by
        have h0 : ((defEnv prog).take p)[preA.length]? = some (t', locA) := by
          rw [hsplitA, List.getElem?_append_right (Nat.le_refl _)]; simp
        rwa [List.getElem?_take_of_lt hlenA] at h0
      have hgetB : (defEnv prog)[preB.length]? = some (t', locB) := by
        rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
      cases locA with
      | slot n => rfl
      | remat e =>
          simp only [matLoc_remat]
          apply matExpr_congr
          intro t'' hu
          have hlt : (defEnv prog).findIdx (fun p => p.1 == t'') < n := by
            rw [← hn]
            exact defEnv_operand_findIdx_lt hord (defEnv_findIdx_entry prog hdc hmemA) hu
          have hmemA'' : t'' ∈ ((defEnv prog).take preA.length).map Prod.fst :=
            operand_mem_take hord hgetA hu
          have hgetB' : (defEnv prog)[preB.length]? = some (t', Loc.remat e) := by
            rw [hgetB, hll]
          have hmemB'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
            operand_mem_take hord hgetB' hu
          have hAeq := ih _ hlt t'' rfl preA.length hmemA''
          have hBeq := ih _ hlt t'' rfl preB.length hmemB''
          rw [← hpreA] at hAeq
          rw [← hpreB] at hBeq
          rw [hAeq, hBeq]
  intro t' p hmem
  exact key _ t' rfl p hmem

theorem matCache_unfold (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {loc : Loc} (hmem : (t, loc) ∈ defEnv prog) :
    matCache prog t = matLoc (matCache prog) loc := by
  rcases matFold_split matInit t (defEnv prog) with hB | hB
  · exact absurd (List.mem_map.mpr ⟨(t, loc), hmem, rfl⟩) hB.1
  obtain ⟨preB, locB, postB, hsplitB, _hpostB, hvalB⟩ := hB
  have hmemB : (t, locB) ∈ defEnv prog := by rw [hsplitB]; simp
  have hll : loc = locB := matCache_last_eq_first prog hdc hmem hmemB
  rw [matCache_eq_matFold, hvalB, hll]
  have hpreB : preB = (defEnv prog).take preB.length := by
    have h1 : preB <+: defEnv prog := by rw [hsplitB]; exact List.prefix_append _ _
    exact List.prefix_iff_eq_take.mp h1
  have hgetB : (defEnv prog)[preB.length]? = some (t, locB) := by
    rw [hsplitB, List.getElem?_append_right (Nat.le_refl _)]; simp
  cases locB with
  | slot n => rfl
  | remat e =>
      simp only [matLoc_remat]
      apply matExpr_congr
      intro t'' hu
      have hgetB' : (defEnv prog)[preB.length]? = some (t, Loc.remat e) := hgetB
      have hmem'' : t'' ∈ ((defEnv prog).take preB.length).map Prod.fst :=
        operand_mem_take hord hgetB' hu
      have heq := matFold_take_eq_matCache prog hdc hord t'' preB.length hmem''
      rw [← hpreB] at heq
      rw [heq, matCache_eq_matFold]

theorem matCache_remat (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {e : Expr} (hmem : (t, Loc.remat e) ∈ defEnv prog) :
    matCache prog t = matExpr (matCache prog) e := by
  rw [matCache_unfold prog hdc hord hmem, matLoc_remat]

theorem matCache_slot (prog : Program) (hdc : DefsConsistent prog) (hord : DefEnvOrdered prog)
    {t : Tmp} {n : Nat} (hmem : (t, Loc.slot n) ∈ defEnv prog) :
    matCache prog t = emitImm (UInt256.ofNat n) ++ [Byte.mload] := by
  rw [matCache_unfold prog hdc hord hmem, matLoc_slot]

theorem matCache_absent (prog : Program) {t : Tmp}
    (hmem : t ∉ (defEnv prog).map Prod.fst) : matCache prog t = emitImm 0 := by
  rw [matCache_eq_matFold, matFold_notMem (defEnv prog) matInit hmem]; rfl

def codeFits (prog : Program) : Prop := (flatBytes prog).length < 2 ^ 32

def chargeDepth (prog : Program) (t : Tmp) : Nat :=
  (chargeCache prog (fun _ => 0) t).length

def stmtChargeDepth (prog : Program) : Stmt → Nat
  | .assign _ (.sload k) => chargeDepth prog k
  | .assign _ _          => 0
  | .sstore key value    => chargeDepth prog value + chargeDepth prog key + 1
  -- The emitted call prologue (`emitStmt`'s `.call` arm) is five zero pushes followed by
  -- the callee and gasFwd materialisations, so the peak stack depth during the prologue is
  -- `max (5 + chargeDepth callee) (6 + chargeDepth gasFwd)`; the sum below dominates both
  -- (mirroring the `.sstore` sum-style count).
  | .call cs             => chargeDepth prog cs.callee + chargeDepth prog cs.gasFwd + 6
  -- CREATE2 operand order (`emitStmt`'s `.create` arm): salt, initSize, initOffset, value —
  -- the value materialise runs with the other three already on the stack, so the peak is
  -- `max (chargeDepth salt) (1 + chargeDepth initSize) (2 + chargeDepth initOffset)
  --      (3 + chargeDepth value)`; the sum below dominates all four.
  | .create cs           =>
      chargeDepth prog cs.salt + chargeDepth prog cs.initSize
        + chargeDepth prog cs.initOffset + chargeDepth prog cs.value + 3

def termChargeDepth (prog : Program) : Term → Nat
  | .branch cond _ _ => chargeDepth prog cond
  | .ret t           => chargeDepth prog t
  | .stop            => 0
  | .jump _          => 0

def maxChargeDepth (prog : Program) : Nat :=
  prog.blocks.foldl (fun acc b =>
    max acc (max (termChargeDepth prog b.term)
                 (b.stmts.foldl (fun a s => max a (stmtChargeDepth prog s)) 0))) 0

def stackFits (prog : Program) : Prop := maxChargeDepth prog ≤ 1024

structure StackRoomOK (prog : Program) : Prop where
  branch : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (cond : Tmp) (thenL elseL : Label),
    blockAt prog L = some b → b.term = .branch cond thenL elseL →
    (chargeCache prog sloadChg cond).length ≤ 1024
  sloadKey : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (t k : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.assign t (.sload k)) →
    (chargeCache prog sloadChg k).length ≤ 1024
  sstore : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (key value : Tmp),
    blockAt prog L = some b → b.stmts[pc]? = some (.sstore key value) →
    (chargeCache prog sloadChg value).length
      + (chargeCache prog sloadChg key).length + 1 ≤ 1024
  ret : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (t : Tmp),
    blockAt prog L = some b → b.term = .ret t →
    (chargeCache prog sloadChg t).length ≤ 1024
  /-- Call-prologue stack room for the callee materialise (runs above the five zero pushes).
  Exactly the `hstkCallee` shape the CALL producer threads. -/
  callCallee : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (cs : CallSpec),
    blockAt prog L = some b → b.stmts[pc]? = some (.call cs) →
    5 + (chargeCache prog sloadChg cs.callee).length ≤ 1024
  /-- Call-prologue stack room for the gasFwd materialise (runs above the five zero pushes
  plus the materialised callee). Exactly the `hstkGasFwd` shape the CALL producer threads. -/
  callGasFwd : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (cs : CallSpec),
    blockAt prog L = some b → b.stmts[pc]? = some (.call cs) →
    6 + (chargeCache prog sloadChg cs.gasFwd).length ≤ 1024
  /-- Create-prologue stack room, one bound per CREATE2 operand at its emission depth
  (salt at 0, initSize at 1, initOffset at 2, value at 3). -/
  createOperands : ∀ (sloadChg : Tmp → ℕ) (L : Label) (b : Block) (pc : Nat) (cs : CreateSpec),
    blockAt prog L = some b → b.stmts[pc]? = some (.create cs) →
    (chargeCache prog sloadChg cs.salt).length ≤ 1024
    ∧ 1 + (chargeCache prog sloadChg cs.initSize).length ≤ 1024
    ∧ 2 + (chargeCache prog sloadChg cs.initOffset).length ≤ 1024
    ∧ 3 + (chargeCache prog sloadChg cs.value).length ≤ 1024

structure IRWellFormed (prog : Program) : Prop where
  defineBeforeUse : RunDefinableG prog
  defsConsistent  : DefsConsistent prog
  entry0          : prog.entry.idx = 0
  cfgClosed       : CFGClosed prog
  defEnvOrdered   : DefEnvOrdered prog
  revalidates     : RevalidatesPerBlock prog
  scopedUses      : ScopedUses prog
  slotAddr        : ∀ (L : Label) (b : Block) (pc : Nat) (t : Tmp),
    blockAt prog L = some b →
    (b.stmts[pc]? = some (.assign t .gas)
      ∨ (∃ k, b.stmts[pc]? = some (.assign t (.sload k)))
      ∨ (∃ cs : CallSpec, b.stmts[pc]? = some (.call cs) ∧ cs.resultTmp = some t)
      ∨ (∃ cs : CreateSpec, b.stmts[pc]? = some (.create cs) ∧ cs.resultTmp = some t)) →
    slotOf t + 63 < 2 ^ 64 ∧ slotOf t < 2 ^ System.Platform.numBits

end Lir.V2
