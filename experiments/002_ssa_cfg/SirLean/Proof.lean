import SirLean.IR
import SirLean.State
import SirLean.SmallStep
import SirLean.Eval
import SirLean.SCCP

namespace Sir

/-! Lemmas and proofs backing `SirLean/Spec.lean`. Each spec-level theorem
`Foo` is proved here as `Foo.proof`. -/

/-! ### `Option`/`Except` plumbing -/

@[simp] theorem liftOption_some {α} (a : α) :
    (liftM (some a) : Except CFGEvalError α) = .ok a := rfl

@[simp] theorem liftOption_none {α} :
    (liftM (none : Option α) : Except CFGEvalError α) = .error .stuck := rfl

@[simp] theorem except_ok_bind {ε α β} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem except_error_bind {ε α β} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

@[simp] theorem except_pure {ε α} (a : α) : (pure a : Except ε α) = .ok a := rfl

@[simp] theorem option_guard (p : Prop) [Decidable p] :
    (guard p : Option Unit) = if p then some () else none := rfl

/-! ### `VarCtx` and per-op lemmas -/

theorem VarCtx.get?_set (vars : VarCtx) (k k' : VarId) (v : Word) :
    (vars.set k v).get? k' = if k = k' then some v else vars.get? k' := rfl

theorem isSome_get?_set {vars : VarCtx} {k k' : VarId} {v : Word}
    (h : (vars.get? k').isSome) : ((vars.set k v).get? k').isSome := by
  rw [VarCtx.get?_set]
  split <;> simp [h]

theorem isSome_get?_set_self {vars : VarCtx} {k : VarId} {v : Word} :
    ((vars.set k v).get? k).isSome := by
  rw [VarCtx.get?_set]
  simp

theorem Op.eval?_isSome {op : Op} {ctx : Env}
    (h : ∀ r ∈ op.refs, (ctx.vars.get? r).isSome) :
    (Op.eval? ctx op).isSome := by
  cases op with
  | const var value => simp [Op.eval?]
  | add32 res lhs rhs =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h lhs (by simp [Op.refs]))
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h rhs (by simp [Op.refs]))
    simp [Op.eval?, hx, hy]
  | lessThan res lhs rhs =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h lhs (by simp [Op.refs]))
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h rhs (by simp [Op.refs]))
    simp [Op.eval?, hx, hy]
  | persistentLoad out addr =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h addr (by simp [Op.refs]))
    simp [Op.eval?, hx]
  | persistentStore addr value =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h addr (by simp [Op.refs]))
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (h value (by simp [Op.refs]))
    simp [Op.eval?, hx, hy]

theorem Op.eval?_mono {op : Op} {ctx ctx' : Env} (h : Op.eval? ctx op = some ctx') :
    ∀ v, (ctx.vars.get? v).isSome → (ctx'.vars.get? v).isSome := by
  intro v hv
  cases op with
  | const var value =>
    simp [Op.eval?] at h
    subst h
    exact isSome_get?_set hv
  | add32 res lhs rhs =>
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    subst h
    exact isSome_get?_set hv
  | lessThan res lhs rhs =>
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    subst h
    exact isSome_get?_set hv
  | persistentLoad out addr =>
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    subst h
    exact isSome_get?_set hv
  | persistentStore addr value =>
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    subst h
    exact hv

theorem Op.eval?_defs {op : Op} {ctx ctx' : Env} (h : Op.eval? ctx op = some ctx') :
    ∀ v ∈ op.defs, (ctx'.vars.get? v).isSome := by
  intro v hv
  cases op with
  | const var value =>
    simp [Op.defs] at hv
    simp [Op.eval?] at h
    subst h hv
    exact isSome_get?_set_self
  | add32 res lhs rhs =>
    simp [Op.defs] at hv
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    subst h hv
    exact isSome_get?_set_self
  | lessThan res lhs rhs =>
    simp [Op.defs] at hv
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, h⟩ := h
    subst h hv
    exact isSome_get?_set_self
  | persistentLoad out addr =>
    simp [Op.defs] at hv
    simp [Op.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    subst h hv
    exact isSome_get?_set_self
  | persistentStore addr value =>
    simp [Op.defs] at hv

theorem EndOp.eval?_isSome {op : EndOp} {ctx : Env}
    (h : ∀ r ∈ op.var_refs, (ctx.vars.get? r).isSome) :
    (op.eval? ctx).isSome := by
  cases op with
  | exit codeVar =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h codeVar (by simp [EndOp.var_refs]))
    simp [EndOp.eval?, hx]
  | jump dst => simp [EndOp.eval?]
  | jump_if j =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h j.cond (by simp [EndOp.var_refs]))
    simp [EndOp.eval?, hx]

theorem EndOp.eval?_goto_mem {op : EndOp} {ctx : Env} {dst : BasicBlockId}
    (h : op.eval? ctx = some (.goto dst)) : dst ∈ op.successors := by
  cases op with
  | exit codeVar => simp [EndOp.eval?, Option.bind_eq_some_iff] at h
  | jump dst' =>
    simp [EndOp.eval?] at h
    simp [EndOp.successors, h]
  | jump_if j =>
    simp [EndOp.eval?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, h⟩ := h
    simp [EndOp.successors]
    split at h <;> simp_all

/-! ### Block-IO transfer lemmas -/

theorem VarCtx.transfer_var_eq_some {sv vars vars' : VarCtx} {p : VarId × VarId} :
    sv.transfer_var vars p = some vars' ↔
      ∃ val, sv.get? p.1 = some val ∧ vars' = vars.set p.2 val := by
  obtain ⟨out, inp⟩ := p
  simp only [VarCtx.transfer_var, Option.map_eq_some_iff]
  constructor
  · rintro ⟨val, hval, h⟩
    exact ⟨val, hval, h.symm⟩
  · rintro ⟨val, hval, h⟩
    exact ⟨val, hval, h.symm⟩

theorem transfer_fold_mono (sv : VarCtx) (l : List (VarId × VarId)) :
    ∀ acc res, l.foldlM sv.transfer_var acc = some res →
      ∀ v, (acc.get? v).isSome → (res.get? v).isSome := by
  induction l with
  | nil =>
    intro acc res h v hv
    simp at h
    subst h
    exact hv
  | cons p l ih =>
    intro acc res h v hv
    rw [List.foldlM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc₁, h₁, h₂⟩ := h
    obtain ⟨val, hval, rfl⟩ := VarCtx.transfer_var_eq_some.mp h₁
    exact ih _ _ h₂ v (isSome_get?_set hv)

theorem transfer_fold_inputs (sv : VarCtx) (l : List (VarId × VarId)) :
    ∀ acc res, l.foldlM sv.transfer_var acc = some res →
      ∀ p ∈ l, (res.get? p.2).isSome := by
  induction l with
  | nil =>
    intro acc res h p hp
    simp at hp
  | cons q l ih =>
    intro acc res h p hp
    rw [List.foldlM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc₁, h₁, h₂⟩ := h
    obtain ⟨val, hval, rfl⟩ := VarCtx.transfer_var_eq_some.mp h₁
    rcases List.mem_cons.mp hp with rfl | hp
    · exact transfer_fold_mono sv l _ _ h₂ _ isSome_get?_set_self
    · exact ih _ _ h₂ p hp

theorem transfer_fold_isSome (sv : VarCtx) (l : List (VarId × VarId)) :
    ∀ acc, (∀ p ∈ l, (sv.get? p.1).isSome) →
      (l.foldlM sv.transfer_var acc).isSome := by
  induction l with
  | nil => intro acc _; simp
  | cons p l ih =>
    intro acc h
    obtain ⟨val, hval⟩ := Option.isSome_iff_exists.mp (h p (by simp))
    rw [List.foldlM_cons]
    have hstep : sv.transfer_var acc p = some (acc.set p.2 val) :=
      VarCtx.transfer_var_eq_some.mpr ⟨val, hval, rfl⟩
    simp only [Option.bind_eq_bind, hstep, Option.bind_some]
    exact ih _ (fun q hq => h q (by simp [hq]))

theorem VarCtx.transfer_block_io_eq_some {sv res : VarCtx} {outs ins : Array VarId}
    (h : sv.transfer_block_io outs ins = some res) :
    outs.size = ins.size ∧
      (outs.zip ins).toList.foldlM sv.transfer_var sv = some res := by
  simp only [VarCtx.transfer_block_io, option_guard, Option.bind_eq_bind] at h
  split at h
  · simp only [Option.bind_some] at h
    refine ⟨‹_›, ?_⟩
    rw [Array.foldlM_toList]
    exact h
  · simp at h

theorem VarCtx.transfer_block_io_mono {sv res : VarCtx} {outs ins : Array VarId}
    (h : sv.transfer_block_io outs ins = some res) :
    ∀ v, (sv.get? v).isSome → (res.get? v).isSome :=
  transfer_fold_mono sv _ _ _ (VarCtx.transfer_block_io_eq_some h).2

theorem VarCtx.transfer_block_io_inputs {sv res : VarCtx} {outs ins : Array VarId}
    (h : sv.transfer_block_io outs ins = some res) :
    ∀ v ∈ ins, (res.get? v).isSome := by
  obtain ⟨hsz, hfold⟩ := VarCtx.transfer_block_io_eq_some h
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hv
  have hzi : i < (outs.zip ins).size := by
    simp only [Array.size_zip]
    omega
  have hp : (outs.zip ins)[i] ∈ (outs.zip ins).toList := by
    rw [Array.mem_toList_iff]
    exact Array.getElem_mem hzi
  rw [Array.getElem_zip] at hp
  exact transfer_fold_inputs sv _ _ _ hfold _ hp

theorem VarCtx.transfer_block_io_isSome {sv : VarCtx} {outs ins : Array VarId}
    (hsz : outs.size = ins.size) (houts : ∀ v ∈ outs, (sv.get? v).isSome) :
    (sv.transfer_block_io outs ins).isSome := by
  simp only [VarCtx.transfer_block_io, option_guard, if_pos hsz, Option.bind_eq_bind,
    Option.bind_some]
  rw [← Array.foldlM_toList]
  refine transfer_fold_isSome sv _ _ ?_
  rintro ⟨a, b⟩ hp
  rw [Array.mem_toList_iff] at hp
  exact houts a (Array.of_mem_zip hp).1

theorem Env.transfer_block_io_eq_some {env e' : Env} {o i : Array VarId} :
    env.transfer_block_io o i = some e' ↔
      ∃ v', env.vars.transfer_block_io o i = some v' ∧
        e' = { env with vars := v' } := by
  constructor
  · intro h
    simp only [Env.transfer_block_io, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨v', hv', h⟩ := h
    exact ⟨v', hv', h.symm⟩
  · rintro ⟨v', hv', rfl⟩
    simp [Env.transfer_block_io, hv']

/-! ### Block evaluation vs. step chains -/

@[simp] theorem Env.mk_eta (e : Env) : (⟨e.vars, e.world⟩ : Env) = e := rfl

theorem resolveSucc?_ok {cfg : ControlFlowGraph} {bbIdx : Fin cfg.blocks.size}
    {dst : BasicBlockId} {dstIdx : Fin cfg.blocks.size}
    (h : cfg.resolveSucc? bbIdx dst = .ok dstIdx) :
    dst ∈ cfg.blocks[bbIdx].successors ∧ dstIdx.val = dst.idx := by
  unfold ControlFlowGraph.resolveSucc? at h
  split at h
  · cases h
    exact ⟨‹_›, rfl⟩
  · cases h

theorem BasicBlock.eval?_eq_some {bb : BasicBlock} {w : World} {vars : VarCtx}
    {w₂ : World} {vars₂ : VarCtx} {cont : Continuation} :
    bb.eval? w vars = some (w₂, vars₂, cont) ↔
      ∃ ctx : Env,
        bb.ops.foldlM (fun ctx op => Op.eval? ctx op) ⟨vars, w⟩ = some ctx ∧
        bb.last.eval? ctx = some cont ∧ ctx.world = w₂ ∧ ctx.vars = vars₂ := by
  simp only [BasicBlock.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨ctx, hctx, c', hc', hw, hv, rfl⟩
    exact ⟨ctx, hctx, hc', hw, hv⟩
  · rintro ⟨ctx, hctx, hcont, hw, hv⟩
    exact ⟨ctx, hctx, cont, hcont, hw, hv, rfl⟩

theorem opsChain {cfg : ControlFlowGraph} {bb : Nat} (hbb : bb < cfg.blocks.size) :
    ∀ (k pc : Nat) (env env' : Env), pc + k = (cfg.blocks[bb]'hbb).ops.size →
      ((cfg.blocks[bb]'hbb).ops.toList.drop pc).foldlM
        (fun ctx op => Op.eval? ctx op) env = some env' →
      CFGSteps cfg (.running bb pc env)
        (.running bb (cfg.blocks[bb]'hbb).ops.size env') := by
  intro k
  induction k with
  | zero =>
    intro pc env env' hsz hfold
    obtain rfl : pc = (cfg.blocks[bb]'hbb).ops.size := by omega
    rw [List.drop_eq_nil_of_le (by simp)] at hfold
    simp at hfold
    subst hfold
    exact .refl
  | succ k ih =>
    intro pc env env' hsz hfold
    have hpc : pc < (cfg.blocks[bb]'hbb).ops.size := by omega
    rw [List.drop_eq_getElem_cons (by simpa using hpc), List.foldlM_cons] at hfold
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hfold
    obtain ⟨env₁, h₁, h₂⟩ := hfold
    have hstep : StepCFG cfg (.running bb pc env) (.running bb (pc + 1) env₁) :=
      .op hbb hpc (by simpa [Array.getElem_toList] using h₁)
    exact Relation.ReflTransGen.head hstep (ih (pc + 1) env₁ env' (by omega) h₂)

/-! ### Big-step soundness (`eval?` ok → small-step reaches `done`) -/

theorem evalGo?_sound {cfg : ControlFlowGraph} :
    ∀ (fuel : Nat) (bbIdx : Fin cfg.blocks.size) (w : World) (vars : VarCtx)
      {t : Termination} {w' : World},
      cfg.evalGo? fuel bbIdx w vars = .ok (t, w') →
      CFGSteps cfg (.running bbIdx.val 0 ⟨vars, w⟩) (.done t w') := by
  intro fuel
  induction fuel with
  | zero =>
    intro bbIdx w vars t w' h
    simp [ControlFlowGraph.evalGo?] at h
  | succ fuel ih =>
    intro bbIdx w vars t w' h
    simp only [ControlFlowGraph.evalGo?, Fin.getElem_fin] at h
    cases hbe : (cfg.blocks[bbIdx.val]'bbIdx.isLt).eval? w vars with
    | none => rw [hbe] at h; simp at h
    | some res =>
      obtain ⟨ctx, hfold, hlast, hw, hv⟩ := BasicBlock.eval?_eq_some.mp hbe
      obtain ⟨w₂, vars₂, cont⟩ := res
      obtain rfl : ctx.world = w₂ := hw
      obtain rfl : ctx.vars = vars₂ := hv
      rw [hbe] at h
      simp only [liftOption_some, except_ok_bind] at h
      rw [← Array.foldlM_toList] at hfold
      have hchain := opsChain (cfg := cfg) (bb := bbIdx.val) bbIdx.isLt
        (cfg.blocks[bbIdx.val]'bbIdx.isLt).ops.size 0 ⟨vars, w⟩ ctx (by omega)
        (by simpa using hfold)
      cases cont with
      | terminated t₂ =>
        simp only [except_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hchain.trans
          (Relation.ReflTransGen.single (.exit bbIdx.isLt rfl hlast))
      | goto dst =>
        simp only [] at h
        cases hres : cfg.resolveSucc? bbIdx dst with
        | error e => rw [hres] at h; simp at h
        | ok dstIdx =>
          rw [hres] at h
          simp only [except_ok_bind] at h
          obtain ⟨hsucc, hval⟩ := resolveSucc?_ok hres
          have hdst : dst.idx < cfg.blocks.size := hval ▸ dstIdx.isLt
          cases htr : ctx.vars.transfer_block_io
              (cfg.blocks[bbIdx.val]'bbIdx.isLt).outputs
              (cfg.blocks[dstIdx.val]'dstIdx.isLt).inputs with
          | none => rw [htr] at h; simp at h
          | some vars₃ =>
            rw [htr] at h
            simp only [liftOption_some, except_ok_bind] at h
            have hrest := ih dstIdx ctx.world vars₃ h
            simp only [hval] at htr hrest
            have hgoto : StepCFG cfg
                (.running bbIdx.val (cfg.blocks[bbIdx.val]'bbIdx.isLt).ops.size ctx)
                (.running dst.idx 0 { ctx with vars := vars₃ }) := by
              refine .goto bbIdx.isLt rfl hlast hdst ?_
              exact Env.transfer_block_io_eq_some.mpr ⟨vars₃, htr, rfl⟩
            exact hchain.trans (Relation.ReflTransGen.head hgoto hrest)

/-! ### Big-step completeness (small-step reaches `done` → `eval?` ok) -/

/-- Proof-internal: `eval?` cannot be entered mid-block, but trace induction
passes through mid-block configurations, so they need a denotable
evaluation. -/
def ControlFlowGraph.cEval? (cfg : ControlFlowGraph) (fuel : Nat) :
    Conf → Except CFGEvalError (Termination × World)
  | .done t w => .ok (t, w)
  | .running bb pc env =>
    if hbb : bb < cfg.blocks.size then do
      let ctx ← ((cfg.blocks[bb]'hbb).ops.toList.drop pc).foldlM
        (m := Option) (fun ctx op => Op.eval? ctx op) env
      let cont ← (cfg.blocks[bb]'hbb).last.eval? ctx
      match cont with
      | .terminated t => return (t, ctx.world)
      | .goto dst => do
        let dstIdx ← cfg.resolveSucc? ⟨bb, hbb⟩ dst
        let vars ← ctx.vars.transfer_block_io (cfg.blocks[bb]'hbb).outputs
          cfg.blocks[dstIdx].inputs
        cfg.evalGo? fuel dstIdx ctx.world vars
    else throw .stuck

theorem cEval?_start {cfg : ControlFlowGraph} {fuel bb : Nat}
    (hbb : bb < cfg.blocks.size) (env : Env) :
    cfg.cEval? fuel (.running bb 0 env) =
      cfg.evalGo? (fuel + 1) ⟨bb, hbb⟩ env.world env.vars := by
  simp only [ControlFlowGraph.cEval?]
  rw [dif_pos hbb]
  simp only [ControlFlowGraph.evalGo?, Fin.getElem_fin]
  cases hfold : ((cfg.blocks[bb]'hbb).ops.toList.drop 0).foldlM
      (m := Option) (fun ctx op => Op.eval? ctx op) env with
  | none =>
    have hbe : (cfg.blocks[bb]'hbb).eval? env.world env.vars = none := by
      simp only [BasicBlock.eval?, Option.bind_eq_bind, Env.mk_eta]
      rw [← Array.foldlM_toList]
      rw [List.drop_zero] at hfold
      simp [hfold]
    rw [hbe]
    simp
  | some ctx =>
    have hfold' :
        (cfg.blocks[bb]'hbb).ops.toList.foldlM (fun ctx op => Op.eval? ctx op) env
          = some ctx := by simpa using hfold
    cases hlast : (cfg.blocks[bb]'hbb).last.eval? ctx with
    | none =>
      have hbe : (cfg.blocks[bb]'hbb).eval? env.world env.vars = none := by
        simp only [BasicBlock.eval?, Option.bind_eq_bind, Env.mk_eta]
        rw [← Array.foldlM_toList, hfold']
        simp [hlast]
      rw [hbe]
      simp [hlast]
    | some cont =>
      have hbe : (cfg.blocks[bb]'hbb).eval? env.world env.vars
          = some (ctx.world, ctx.vars, cont) := by
        simp only [BasicBlock.eval?, Option.bind_eq_bind, Env.mk_eta]
        rw [← Array.foldlM_toList, hfold']
        simp [hlast]
      rw [hbe]
      simp only [liftOption_some, except_ok_bind, hlast]
      cases cont with
      | terminated t => rfl
      | goto dst => rfl

theorem cEval?_back {cfg : ControlFlowGraph} {c c' : Conf}
    (hstep : StepCFG cfg c c') {t : Termination} {w' : World}
    (h : ∃ fuel, cfg.cEval? fuel c' = .ok (t, w')) :
    ∃ fuel, cfg.cEval? fuel c = .ok (t, w') := by
  obtain ⟨fuel, hc⟩ := h
  cases hstep with
  | op hbb hpc hop =>
    rename_i bb pc e e'
    refine ⟨fuel, ?_⟩
    rw [← hc]
    simp only [ControlFlowGraph.cEval?]
    rw [dif_pos hbb, dif_pos hbb]
    rw [List.drop_eq_getElem_cons (by simpa using hpc), List.foldlM_cons]
    have hop' : Op.eval? e ((cfg.blocks[bb]'hbb).ops.toList[pc]'(by simpa using hpc))
        = some e' := by simpa [Array.getElem_toList] using hop
    rw [hop']
    simp
  | exit hbb hpc hend =>
    rename_i bb pc e t₂
    have hend' : (cfg.blocks[bb]'hbb).last.eval? e = some (.terminated t₂) := hend
    simp only [ControlFlowGraph.cEval?] at hc
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨0, ?_⟩
    simp only [ControlFlowGraph.cEval?]
    rw [dif_pos hbb]
    rw [List.drop_eq_nil_of_le (by simp [hpc])]
    simp [hend']
  | goto hbb hpc hend hdst htransfer =>
    rename_i bb pc e dst e'
    have hend' : (cfg.blocks[bb]'hbb).last.eval? e = some (.goto dst) := hend
    obtain ⟨v', hv', rfl⟩ := Env.transfer_block_io_eq_some.mp htransfer
    rw [cEval?_start hdst] at hc
    refine ⟨fuel + 1, ?_⟩
    simp only [ControlFlowGraph.cEval?]
    rw [dif_pos hbb]
    rw [List.drop_eq_nil_of_le (by simp [hpc])]
    simp only [List.foldlM_nil, Option.pure_def, liftOption_some, except_ok_bind, hend']
    have hsucc : dst ∈ (cfg.blocks[bb]'hbb).successors := EndOp.eval?_goto_mem hend'
    rw [ControlFlowGraph.resolveSucc?]
    simp only [Fin.getElem_fin]
    rw [dif_pos hsucc]
    simp only [except_ok_bind]
    simp only [ControlFlowGraph.succ_to_idx]
    rw [hv']
    simpa using hc

theorem ControlFlowGraph.eval?_iff_steps.proof
    (cfg : ControlFlowGraph) (w : World) (t : Termination) (w' : World) :
    (∃ fuel, cfg.eval? w fuel = .ok (t, w')) ↔
      CFGSteps cfg (cfg.initialConf w) (.done t w') := by
  constructor
  · rintro ⟨fuel, h⟩
    rw [ControlFlowGraph.eval?] at h
    have := evalGo?_sound fuel cfg.entry w .empty h
    simpa [ControlFlowGraph.initialConf] using this
  · intro h
    have hex : ∀ c, CFGSteps cfg c (.done t w') →
        ∃ fuel, cfg.cEval? fuel c = .ok (t, w') := by
      intro c hc
      induction hc using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨0, rfl⟩
      | head hstep _ ih => exact cEval?_back hstep ih
    obtain ⟨fuel, hc⟩ := hex _ h
    refine ⟨fuel + 1, ?_⟩
    rw [ControlFlowGraph.eval?]
    rw [show cfg.initialConf w = .running cfg.entry.val 0 ⟨.empty, w⟩ from rfl] at hc
    rw [cEval?_start cfg.entry.isLt] at hc
    simpa using hc

/-! ### Progress -/

/-- Variables guaranteed to be bound at position `(bb, pc)`: block inputs,
defs of already-executed ops, and anything defined on every path from the
entry. -/
def Avail (cfg : ControlFlowGraph) (bb : Fin cfg.blocks.size) (pc : Nat)
    (v : VarId) : Prop :=
  v ∈ cfg.blocks[bb].inputs
  ∨ (∃ i, ∃ hi : i < cfg.blocks[bb].ops.size, i < pc ∧ v ∈ cfg.blocks[bb].ops[i].defs)
  ∨ cfg.inner.DefinedOnAllPaths v bb

def WF (cfg : ControlFlowGraph) : Conf → Prop
  | .done _ _ => True
  | .running bb pc env =>
    ∃ hbb : bb < cfg.blocks.size,
      pc ≤ (cfg.blocks[bb]'hbb).ops.size ∧
      ∀ v, Avail cfg ⟨bb, hbb⟩ pc v → (env.vars.get? v).isSome

theorem mem_defs_up_to_iff {bb : BasicBlock} {pc : Nat} (hpc : pc < bb.ops.size)
    {v : VarId} :
    v ∈ bb.defs_up_to ⟨pc, hpc⟩ ↔
      v ∈ bb.inputs ∨ ∃ i, ∃ hi : i < bb.ops.size, i < pc ∧ v ∈ bb.ops[i].defs := by
  simp only [BasicBlock.defs_up_to, Array.mem_append, Array.mem_flatMap]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨op, hop, hdef⟩
    rw [Array.mem_extract_iff_getElem] at hop
    obtain ⟨k, hk, rfl⟩ := hop
    simp at hk
    refine ⟨k, by omega, by omega, by simpa using hdef⟩
  · rintro ⟨i, hi, hlt, hdef⟩
    refine ⟨bb.ops[i], ?_, hdef⟩
    rw [Array.mem_extract_iff_getElem]
    refine ⟨i, by simp; omega, by simp⟩

theorem mem_defs_iff {bb : BasicBlock} {v : VarId} :
    v ∈ bb.defs ↔
      v ∈ bb.inputs ∨ ∃ i, ∃ hi : i < bb.ops.size, v ∈ bb.ops[i].defs := by
  simp only [BasicBlock.defs, Array.mem_append, Array.mem_flatMap]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨op, hop, hdef⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hop
    exact ⟨i, hi, hdef⟩
  · rintro ⟨i, hi, hdef⟩
    exact ⟨bb.ops[i], Array.getElem_mem hi, hdef⟩

theorem wf_init (cfg : ControlFlowGraph) (w : World) :
    WF cfg (cfg.initialConf w) := by
  simp only [ControlFlowGraph.initialConf, WF]
  refine ⟨cfg.entry.isLt, by omega, ?_⟩
  intro v hav
  simp only [Avail] at hav
  rcases hav with hin | ⟨i, hi, hlt, _⟩ | hnp
  · exfalso
    have h0 := cfg.entry_no_inputs
    rw [Array.isEmpty_iff] at h0
    rw [show (⟨cfg.entry.val, cfg.entry.isLt⟩ : Fin cfg.blocks.size) = cfg.entry from
      Fin.eta .., h0] at hin
    simp at hin
  · omega
  · exact absurd (InnerCFG.undef_at_entry cfg.inner v) hnp

theorem wf_step {cfg : ControlFlowGraph} {c c' : Conf}
    (hstep : StepCFG cfg c c') (hwf : WF cfg c) : WF cfg c' := by
  cases hstep with
  | op hbb hpc hop =>
    rename_i bb pc e e'
    simp only [WF] at hwf ⊢
    obtain ⟨hbb', hpc', henv⟩ := hwf
    refine ⟨hbb, by omega, ?_⟩
    intro v hav
    simp only [Avail] at hav
    rcases hav with hin | ⟨i, hi, hlt, hdef⟩ | hnp
    · exact Op.eval?_mono hop v (henv v (Or.inl hin))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact Op.eval?_mono hop v (henv v (Or.inr (Or.inl ⟨i, hi, hlt', hdef⟩)))
      · exact Op.eval?_defs hop v hdef
    · exact Op.eval?_mono hop v (henv v (Or.inr (Or.inr hnp)))
  | exit hbb hpc hend =>
    simp only [WF]
  | goto hbb hpc hend hdst htransfer =>
    rename_i bb pc e dst e'
    have hend' : (cfg.blocks[bb]'hbb).last.eval? e = some (.goto dst) := hend
    simp only [WF] at hwf ⊢
    obtain ⟨hbb', hpc', henv⟩ := hwf
    subst hpc
    obtain ⟨v', hv', rfl⟩ := Env.transfer_block_io_eq_some.mp htransfer
    refine ⟨hdst, by omega, ?_⟩
    intro v hav
    simp only [Avail] at hav
    rcases hav with hin | ⟨i, hi, hlt, _⟩ | hnp
    · exact VarCtx.transfer_block_io_inputs hv' v hin
    · omega
    · by_cases hv : v ∈ (cfg.blocks[bb]'hbb).defs
      · refine VarCtx.transfer_block_io_mono hv' v ?_
        rcases mem_defs_iff.mp hv with hin' | ⟨i, hi, hdef⟩
        · exact henv v (Or.inl hin')
        · exact henv v (Or.inr (Or.inl ⟨i, hi, by omega, hdef⟩))
      · refine VarCtx.transfer_block_io_mono hv' v ?_
        refine henv v (Or.inr (Or.inr ?_))
        intro hp
        exact hnp (hp.tail ⟨EndOp.eval?_goto_mem hend', hv⟩)

theorem wf_progress {cfg : ControlFlowGraph} {c : Conf} (hwf : WF cfg c) :
    (∃ t w', c = .done t w') ∨ (∃ c', StepCFG cfg c c') := by
  cases c with
  | done t w => exact Or.inl ⟨t, w, rfl⟩
  | running bb pc env =>
    right
    simp only [WF] at hwf
    obtain ⟨hbb, hpc, henv⟩ := hwf
    obtain ⟨hopv, hendv, houtv⟩ := cfg.refs_valid
    rcases Nat.lt_or_ge pc (cfg.blocks[bb]'hbb).ops.size with hlt | hge
    · have hrefs : ∀ r ∈ ((cfg.blocks[bb]'hbb).ops[pc]'hlt).refs,
          (env.vars.get? r).isSome := by
        intro r hr
        rcases hopv ⟨bb, hbb⟩ ⟨pc, hlt⟩ r hr with hd | hnp
        · rcases (mem_defs_up_to_iff hlt).mp hd with hin | ⟨i, hi, hlti, hdef⟩
          · exact henv r (Or.inl hin)
          · exact henv r (Or.inr (Or.inl ⟨i, hi, hlti, hdef⟩))
        · exact henv r (Or.inr (Or.inr hnp))
      obtain ⟨env', henv'⟩ := Option.isSome_iff_exists.mp (Op.eval?_isSome hrefs)
      exact ⟨_, .op hbb hlt henv'⟩
    · have hpceq : pc = (cfg.blocks[bb]'hbb).ops.size := by omega
      have hat : ∀ r, r ∈ (cfg.blocks[bb]'hbb).defs ∨
          cfg.inner.DefinedOnAllPaths r ⟨bb, hbb⟩ →
          (env.vars.get? r).isSome := by
        intro r hd
        rcases hd with hd | hnp
        · rcases mem_defs_iff.mp hd with hin | ⟨i, hi, hdef⟩
          · exact henv r (Or.inl hin)
          · exact henv r (Or.inr (Or.inl ⟨i, hi, by omega, hdef⟩))
        · exact henv r (Or.inr (Or.inr hnp))
      have hrefs : ∀ r ∈ (cfg.blocks[bb]'hbb).last.var_refs,
          (env.vars.get? r).isSome := by
        intro r hr
        exact hat r (hendv ⟨bb, hbb⟩ r hr)
      obtain ⟨cont, hcont⟩ := Option.isSome_iff_exists.mp (EndOp.eval?_isSome hrefs)
      cases cont with
      | terminated t => exact ⟨_, .exit hbb hpceq hcont⟩
      | goto dst =>
        have hsucc : dst ∈ (cfg.blocks[bb]'hbb).successors :=
          EndOp.eval?_goto_mem hcont
        obtain ⟨hdst, hsz⟩ :=
          cfg.blocks_valid (cfg.blocks[bb]'hbb) (Array.getElem_mem hbb) dst hsucc
        have houts : ∀ v ∈ (cfg.blocks[bb]'hbb).outputs, (env.vars.get? v).isSome :=
          fun v hv => hat v (houtv ⟨bb, hbb⟩ v hv)
        obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp
          (VarCtx.transfer_block_io_isSome hsz houts)
        exact ⟨_, .goto hbb hpceq hcont hdst
          (Env.transfer_block_io_eq_some.mpr ⟨v', hv', rfl⟩)⟩

theorem ControlFlowGraph.progress.proof
    (cfg : ControlFlowGraph) (w : World) (c : Conf)
    (hreach : CFGSteps cfg (cfg.initialConf w) c) :
    (∃ t w', c = .done t w') ∨ (∃ c', StepCFG cfg c c') := by
  refine wf_progress ?_
  induction hreach with
  | refl => exact wf_init cfg w
  | tail _ hstep ih => exact wf_step hstep ih

/-! ## SCCP semantic preservation -/

/-! ### `Op.eval?` / `EndOp.eval?` characterizations -/

theorem Op.eval?_const_iff {e e' : Env} {v : VarId} {w : Word} :
    Op.eval? e (.const v w) = some e' ↔ e' = { e with vars := e.vars.set v w } := by
  simp [Op.eval?, eq_comm]

theorem Op.eval?_add32_iff {e e' : Env} {r a b : VarId} :
    Op.eval? e (.add32 r a b) = some e' ↔
      ∃ x y, e.vars.get? a = some x ∧ e.vars.get? b = some y ∧
        e' = { e with vars := e.vars.set r (x + y) } := by
  simp only [Op.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, y, hx, hy, h.symm⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨x, hx, y, hy, h.symm⟩

theorem Op.eval?_lessThan_iff {e e' : Env} {r a b : VarId} :
    Op.eval? e (.lessThan r a b) = some e' ↔
      ∃ x y, e.vars.get? a = some x ∧ e.vars.get? b = some y ∧
        e' = { e with vars := e.vars.set r (if x < y then 1 else 0) } := by
  simp only [Op.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, y, hx, hy, h.symm⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨x, hx, y, hy, h.symm⟩

theorem Op.eval?_load_iff {e e' : Env} {out addr : VarId} :
    Op.eval? e (.persistentLoad out addr) = some e' ↔
      ∃ x, e.vars.get? addr = some x ∧
        e' = { e with vars := e.vars.set out (e.world.get x) } := by
  simp only [Op.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h.symm⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, h.symm⟩

theorem Op.eval?_store_iff {e e' : Env} {addr v : VarId} :
    Op.eval? e (.persistentStore addr v) = some e' ↔
      ∃ x y, e.vars.get? addr = some x ∧ e.vars.get? v = some y ∧
        e' = { e with world := e.world.set x y } := by
  simp only [Op.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, y, hx, hy, h.symm⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨x, hx, y, hy, h.symm⟩

theorem EndOp.eval?_exit_iff {e : Env} {v : VarId} {c : Continuation} :
    EndOp.eval? (.exit v) e = some c ↔
      ∃ w, e.vars.get? v = some w ∧ c = .terminated (.exited w) := by
  simp only [EndOp.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩

theorem EndOp.eval?_jump_iff {e : Env} {d : BasicBlockId} {c : Continuation} :
    EndOp.eval? (.jump d) e = some c ↔ c = .goto d := by
  simp [EndOp.eval?, eq_comm]

theorem EndOp.eval?_jump_if_iff {e : Env} {j : JumpIf} {c : Continuation} :
    EndOp.eval? (.jump_if j) e = some c ↔
      ∃ w, e.vars.get? j.cond = some w ∧
        c = .goto (if w = 0 then j.dst_if_zero else j.dst_if_non_zero) := by
  simp only [EndOp.eval?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, h.symm⟩

/-! ### Boundness of refs at well-formed configurations -/

theorem wf_op_refs {cfg : ControlFlowGraph} {bb pc : Nat} {env : Env}
    (hwf : WF cfg (.running bb pc env)) (hbb : bb < cfg.blocks.size)
    (hpc : pc < (cfg.blocks[bb]'hbb).ops.size) :
    ∀ r ∈ ((cfg.blocks[bb]'hbb).ops[pc]'hpc).refs, (env.vars.get? r).isSome := by
  simp only [WF] at hwf
  obtain ⟨hbb', hpc', henv⟩ := hwf
  intro r hr
  rcases cfg.refs_valid.1 ⟨bb, hbb⟩ ⟨pc, hpc⟩ r hr with hd | hnp
  · rcases (mem_defs_up_to_iff hpc).mp hd with hin | ⟨i, hi, hlti, hdef⟩
    · exact henv r (Or.inl hin)
    · exact henv r (Or.inr (Or.inl ⟨i, hi, hlti, hdef⟩))
  · exact henv r (Or.inr (Or.inr hnp))

theorem wf_end_refs {cfg : ControlFlowGraph} {bb pc : Nat} {env : Env}
    (hwf : WF cfg (.running bb pc env)) (hbb : bb < cfg.blocks.size)
    (hpc : pc = (cfg.blocks[bb]'hbb).ops.size) :
    ∀ r ∈ (cfg.blocks[bb]'hbb).last.var_refs, (env.vars.get? r).isSome := by
  simp only [WF] at hwf
  obtain ⟨hbb', hpc', henv⟩ := hwf
  intro r hr
  rcases cfg.refs_valid.2.1 ⟨bb, hbb⟩ r hr with hd | hnp
  · rcases mem_defs_iff.mp hd with hin | ⟨i, hi, hdef⟩
    · exact henv r (Or.inl hin)
    · have hi' : i < (cfg.blocks[bb]'hbb).ops.size := hi
      exact henv r (Or.inr (Or.inl ⟨i, hi', by omega, hdef⟩))
  · exact henv r (Or.inr (Or.inr hnp))

namespace SCCP

variable {cfg : ControlFlowGraph}

/-! ### Lattice / abstract-state order facts -/

theorem AbsState.eq_of_le_of_le {s t : AbsState cfg} (hst : s ≤ t) (hts : t ≤ s) : s = t := by
  obtain ⟨hr1, hv1⟩ := AbsState.le_iff.mp hst
  obtain ⟨hr2, hv2⟩ := AbsState.le_iff.mp hts
  obtain ⟨sr, sv⟩ := s
  obtain ⟨tr, tv⟩ := t
  simp only [AbsState.mk.injEq]
  constructor
  · ext i hi
    have h1 := hr1 i hi
    have h2 := hr2 i hi
    cases hs : sr[i] <;> cases ht : tr[i] <;> simp_all
  · ext i hi
    exact le_antisymm (hv1 i hi) (hv2 i hi)

theorem Value.le_overdefined (v : Value) : v ≤ Value.overdefined := by
  show Value.le v .overdefined
  cases v <;> trivial

theorem Value.const_le_const {a b : Word} (h : Value.const a ≤ Value.const b) : a = b := h

theorem Value.not_const_le_undef {a : Word} : ¬ (Value.const a ≤ Value.undef) := fun h => h

theorem Value.binop_sound {f : Word → Word → Word} {va vb : Value} {x y : Word}
    (ha : Value.const x ≤ va) (hb : Value.const y ≤ vb) :
    Value.const (f x y) ≤ Value.binop f va vb := by
  have ha' : Value.le (.const x) va := ha
  have hb' : Value.le (.const y) vb := hb
  show Value.le (Value.const (f x y)) (Value.binop f va vb)
  cases va <;> cases vb <;> simp_all [Value.le, Value.binop]

/-! ### Fixpoint extraction -/

theorem foldl_fix {α β : Type*} [Preorder α] {f : α → β → α} (hf : ∀ a b, a ≤ f a b)
    (anti : ∀ a b : α, a ≤ b → b ≤ a → a = b) :
    ∀ (l : List β) (a : α), l.foldl f a = a → ∀ b ∈ l, f a b = a := by
  intro l
  induction l with
  | nil =>
    intro a _ b hb
    simp at hb
  | cons x xs ih =>
    intro a h b hb
    rw [List.foldl_cons] at h
    have hax : f a x = a := by
      have h1 := foldl_le hf xs (f a x)
      rw [h] at h1
      exact anti _ _ h1 (hf a x)
    rw [hax] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hax
    · exact ih a h b hb

theorem foldl_fix_array {α β : Type*} [Preorder α] {f : α → β → α} (hf : ∀ a b, a ≤ f a b)
    (anti : ∀ a b : α, a ≤ b → b ≤ a → a = b)
    (xs : Array β) (a : α) (h : xs.foldl f a = a) : ∀ b ∈ xs, f a b = a := by
  intro b hb
  rw [← Array.foldl_toList] at h
  exact foldl_fix hf anti xs.toList a h b (by simpa using hb)

theorem step_solve (s : AbsState cfg) : step (solve s) = solve s := by
  fun_induction solve s with
  | case1 s s' h => exact h
  | case2 s s' h ih => exact ih

theorem le_solve (s : AbsState cfg) : s ≤ solve s := by
  fun_induction solve s with
  | case1 s s' h => exact le_rfl
  | case2 s s' h ih => exact le_trans (le_step s) ih

theorem step_analyze (cfg : ControlFlowGraph) : step (analyze cfg) = analyze cfg :=
  step_solve _

theorem analyze_entry_reachable (cfg : ControlFlowGraph) :
    (analyze cfg).reachable[cfg.entry.val]'cfg.entry.isLt = true := by
  refine (AbsState.le_iff.mp (le_solve (AbsState.init cfg))).1 cfg.entry.val cfg.entry.isLt ?_
  show ((Vector.replicate cfg.blocks.size false).set cfg.entry.val true
    cfg.entry.isLt)[cfg.entry.val] = true
  simp

theorem join_fix {σ : AbsState cfg} {v : VarId} {x : Value} (h : σ.join v x = σ) :
    x ≤ σ.get v := by
  cases hidx : (allDefs cfg).finIdxOf? v with
  | none =>
    unfold AbsState.get
    rw [hidx]
    exact Value.le_overdefined x
  | some i =>
    unfold AbsState.join at h
    rw [hidx] at h
    have hv : σ.vals.set i.val (σ.vals[i] ⊔ x) i.isLt = σ.vals := congrArg AbsState.vals h
    have hgi := congrArg (fun ve => ve[i.val]'i.isLt) hv
    simp only [Vector.getElem_set_self] at hgi
    unfold AbsState.get
    rw [hidx]
    exact sup_eq_left.mp hgi

theorem markReachable_fix {σ : AbsState cfg} {b : Nat} {hb : b < cfg.blocks.size}
    (h : σ.markReachable b hb = σ) : σ.reachable[b] = true := by
  have hr : σ.reachable.set b true hb = σ.reachable := congrArg AbsState.reachable h
  have := congrArg (fun ve => ve[b]'hb) hr
  simpa using this

theorem transferArg_fix {σ : AbsState cfg} {p : VarId × VarId} (h : transferArg σ p = σ) :
    σ.get p.1 ≤ σ.get p.2 :=
  join_fix h

theorem transferEdge_fix {σ : AbsState cfg} {outputs : Array VarId} {dst : BasicBlockId}
    (hdst : dst.idx < cfg.blocks.size) (h : transferEdge σ outputs dst = σ) :
    σ.reachable[dst.idx] = true ∧
      ∀ p ∈ outputs.zip (cfg.blocks[dst.idx]'hdst).inputs, σ.get p.1 ≤ σ.get p.2 := by
  unfold transferEdge at h
  rw [dif_pos hdst] at h
  have hle : σ.markReachable dst.idx hdst ≤ σ := by
    have h1 := foldl_le_array (fun a p => le_transferArg a p)
      (outputs.zip (cfg.blocks[dst.idx]'hdst).inputs) (σ.markReachable dst.idx hdst)
    rw [h] at h1
    exact h1
  have hmark : σ.markReachable dst.idx hdst = σ :=
    AbsState.eq_of_le_of_le hle (AbsState.le_markReachable σ dst.idx hdst)
  rw [hmark] at h
  refine ⟨markReachable_fix hmark, fun p hp => transferArg_fix ?_⟩
  exact foldl_fix_array (fun a p => le_transferArg a p)
    (fun _ _ => AbsState.eq_of_le_of_le) _ _ h p hp

theorem transferEdge_both_fix {σ : AbsState cfg} {o : Array VarId} {z nz : BasicBlockId}
    (h : transferEdge (transferEdge σ o z) o nz = σ) :
    transferEdge σ o z = σ ∧ transferEdge σ o nz = σ := by
  have h1 : transferEdge σ o z ≤ σ := by
    have h2 := le_transferEdge (transferEdge σ o z) o nz
    rw [h] at h2
    exact h2
  have hA : transferEdge σ o z = σ := AbsState.eq_of_le_of_le h1 (le_transferEdge σ o z)
  rw [hA] at h
  exact ⟨hA, h⟩

theorem transferBlock_fix {σ : AbsState cfg} (hfix : step σ = σ) (b : Fin cfg.blocks.size) :
    transferBlock σ b = σ := by
  unfold step at hfix
  exact foldl_fix (fun a b => le_transferBlock a b) (fun _ _ => AbsState.eq_of_le_of_le)
    _ _ hfix b (List.mem_finRange b)

theorem block_fix {σ : AbsState cfg} (hfix : step σ = σ) {b : Fin cfg.blocks.size}
    (hr : σ.reachable[b] = true) :
    (∀ op ∈ cfg.blocks[b].ops, transferOp σ op = σ) ∧ transferLast σ cfg.blocks[b] = σ := by
  have h := transferBlock_fix hfix b
  unfold transferBlock at h
  rw [if_pos hr] at h
  have hle : cfg.blocks[b].ops.foldl transferOp σ ≤ σ := by
    have h1 := le_transferLast (cfg.blocks[b].ops.foldl transferOp σ) cfg.blocks[b]
    rw [h] at h1
    exact h1
  have hops : cfg.blocks[b].ops.foldl transferOp σ = σ :=
    AbsState.eq_of_le_of_le hle (foldl_le_array (fun a op => le_transferOp a op) _ _)
  rw [hops] at h
  exact ⟨foldl_fix_array (fun a op => le_transferOp a op)
    (fun _ _ => AbsState.eq_of_le_of_le) _ _ hops, h⟩

theorem transferLast_jump_fix {σ : AbsState cfg} {bbk : BasicBlock} {d : BasicBlockId}
    (h : bbk.last = .jump d) (hfix : transferLast σ bbk = σ) :
    transferEdge σ bbk.outputs d = σ := by
  unfold transferLast at hfix
  rw [h] at hfix
  exact hfix

theorem transferLast_jump_if_fix {σ : AbsState cfg} {bbk : BasicBlock} {j : JumpIf}
    (h : bbk.last = .jump_if j) (hfix : transferLast σ bbk = σ) :
    (∀ w, σ.get j.cond = .const w →
      transferEdge σ bbk.outputs (if w = 0 then j.dst_if_zero else j.dst_if_non_zero) = σ)
    ∧ (σ.get j.cond = .overdefined →
      transferEdge σ bbk.outputs j.dst_if_zero = σ
        ∧ transferEdge σ bbk.outputs j.dst_if_non_zero = σ) := by
  unfold transferLast at hfix
  split at hfix
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
    split at hfix
    · rename_i hcond
      refine ⟨fun w hw => ?_, fun hw => ?_⟩
      · rw [hw] at hcond
        cases hcond
      · rw [hw] at hcond
        cases hcond
    · rename_i w' hcond
      refine ⟨fun w hw => ?_, fun hw => ?_⟩
      · rw [hcond] at hw
        cases hw
        exact hfix
      · rw [hcond] at hw
        cases hw
    · rename_i hcond
      refine ⟨fun w hw => ?_, fun _ => transferEdge_both_fix hfix⟩
      rw [hcond] at hw
      cases hw

/-! ### Concrete soundness of the analysis

`Models σ vars`: every concretely bound variable is over-approximated by the
abstract state. `SInv` carries this plus reachability of the current block
along any concrete trace. -/

def Models (σ : AbsState cfg) (vars : VarCtx) : Prop :=
  ∀ v w, vars.get? v = some w → Value.const w ≤ σ.get v

theorem models_empty (σ : AbsState cfg) : Models σ .empty := by
  intro v w h
  simp [VarCtx.empty, VarCtx.get?] at h

theorem Models.set {σ : AbsState cfg} {vars : VarCtx} (h : Models σ vars) {v : VarId}
    {w : Word} (hv : Value.const w ≤ σ.get v) : Models σ (vars.set v w) := by
  intro u x hx
  rw [VarCtx.get?_set] at hx
  split at hx
  · rename_i heq
    cases hx
    exact heq ▸ hv
  · exact h u x hx

theorem models_transfer_fold {σ : AbsState cfg} {sv : VarCtx} (hsv : Models σ sv) :
    ∀ (l : List (VarId × VarId)), (∀ p ∈ l, σ.get p.1 ≤ σ.get p.2) →
      ∀ acc res, l.foldlM sv.transfer_var acc = some res → Models σ acc → Models σ res := by
  intro l
  induction l with
  | nil =>
    intro _ acc res h hacc
    simp at h
    subst h
    exact hacc
  | cons p l ih =>
    intro hl acc res h hacc
    rw [List.foldlM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨acc₁, h₁, h₂⟩ := h
    obtain ⟨val, hval, rfl⟩ := VarCtx.transfer_var_eq_some.mp h₁
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ _ h₂ ?_
    exact hacc.set (le_trans (hsv _ _ hval) (hl p (List.mem_cons_self ..)))

theorem Models.transfer_block_io {σ : AbsState cfg} {sv res : VarCtx}
    {outs ins : Array VarId} (hsv : Models σ sv)
    (hflow : ∀ p ∈ outs.zip ins, σ.get p.1 ≤ σ.get p.2)
    (h : sv.transfer_block_io outs ins = some res) : Models σ res := by
  obtain ⟨-, hfold⟩ := VarCtx.transfer_block_io_eq_some h
  exact models_transfer_fold hsv _ (fun p hp => hflow p (Array.mem_toList_iff.mp hp))
    _ _ hfold hsv

def SInv (cfg : ControlFlowGraph) (σ : AbsState cfg) : Conf → Prop
  | .done _ _ => True
  | .running bb _ env =>
    ∃ hbb : bb < cfg.blocks.size, σ.reachable[bb] = true ∧ Models σ env.vars

theorem sinv_init {σ : AbsState cfg}
    (hentry : σ.reachable[cfg.entry.val]'cfg.entry.isLt = true) (w : World) :
    SInv cfg σ (cfg.initialConf w) := by
  exact ⟨cfg.entry.isLt, hentry, models_empty σ⟩

/-- The destination of a concretely taken edge out of a reachable block is
reachable, and the abstract values flow along it. -/
theorem taken_edge_fix {σ : AbsState cfg} {bb : Nat} {hbb : bb < cfg.blocks.size}
    (hlastfix : transferLast σ (cfg.blocks[bb]'hbb) = σ) {e : Env} (hm : Models σ e.vars)
    {dst : BasicBlockId}
    (hend : StepEndOp e (cfg.blocks[bb]'hbb).last (.goto dst)) :
    transferEdge σ (cfg.blocks[bb]'hbb).outputs dst = σ := by
  cases hlast : (cfg.blocks[bb]'hbb).last with
  | exit v =>
    have hend' : EndOp.eval? (.exit v) e = some (.goto dst) := hlast ▸ hend
    obtain ⟨w, -, h⟩ := EndOp.eval?_exit_iff.mp hend'
    cases h
  | jump d =>
    have hend' : EndOp.eval? (.jump d) e = some (.goto dst) := hlast ▸ hend
    have hgd := EndOp.eval?_jump_iff.mp hend'
    cases hgd
    exact transferLast_jump_fix hlast hlastfix
  | jump_if j =>
    have hend' : EndOp.eval? (.jump_if j) e = some (.goto dst) := hlast ▸ hend
    obtain ⟨w, hw, hdst⟩ := EndOp.eval?_jump_if_iff.mp hend'
    obtain rfl : dst = if w = 0 then j.dst_if_zero else j.dst_if_non_zero := by
      cases hdst
      rfl
    have hc := hm j.cond w hw
    obtain ⟨hconst, hover⟩ := transferLast_jump_if_fix hlast hlastfix
    cases hg : σ.get j.cond with
    | undef =>
      rw [hg] at hc
      exact absurd hc Value.not_const_le_undef
    | const w₀ =>
      rw [hg] at hc
      obtain rfl : w = w₀ := Value.const_le_const hc
      exact hconst w hg
    | overdefined =>
      obtain ⟨hz, hnz⟩ := hover hg
      split
      · exact hz
      · exact hnz

theorem sinv_step {σ : AbsState cfg} (hfix : step σ = σ) {c c' : Conf}
    (hstep : StepCFG cfg c c') (hinv : SInv cfg σ c) : SInv cfg σ c' := by
  cases hstep with
  | op hbb hpc hop =>
    rename_i bb pc e e'
    simp only [SInv] at hinv ⊢
    obtain ⟨hbb', hreach, hm⟩ := hinv
    refine ⟨hbb, hreach, ?_⟩
    have hopfix : transferOp σ ((cfg.blocks[bb]'hbb).ops[pc]'hpc) = σ :=
      (block_fix hfix (b := ⟨bb, hbb⟩) hreach).1 _ (Array.getElem_mem hpc)
    cases hopc : (cfg.blocks[bb]'hbb).ops[pc]'hpc with
    | const v w =>
      rw [hopc] at hop hopfix
      obtain rfl := Op.eval?_const_iff.mp hop
      exact hm.set (join_fix hopfix)
    | add32 r a b =>
      rw [hopc] at hop hopfix
      obtain ⟨x, y, hx, hy, rfl⟩ := Op.eval?_add32_iff.mp hop
      refine hm.set (le_trans (Value.binop_sound (hm a x hx) (hm b y hy)) ?_)
      exact join_fix hopfix
    | lessThan r a b =>
      rw [hopc] at hop hopfix
      obtain ⟨x, y, hx, hy, rfl⟩ := Op.eval?_lessThan_iff.mp hop
      refine hm.set (le_trans
        (Value.binop_sound (f := fun x y => if x < y then 1 else 0)
          (hm a x hx) (hm b y hy)) ?_)
      exact join_fix hopfix
    | persistentLoad out addr =>
      rw [hopc] at hop hopfix
      obtain ⟨x, hx, rfl⟩ := Op.eval?_load_iff.mp hop
      have hover : σ.get out = .overdefined :=
        le_antisymm (Value.le_overdefined _) (join_fix hopfix)
      exact hm.set (hover ▸ Value.le_overdefined _)
    | persistentStore addr v =>
      rw [hopc] at hop
      obtain ⟨x, y, hx, hy, rfl⟩ := Op.eval?_store_iff.mp hop
      exact hm
  | exit hbb hpc hend =>
    simp only [SInv]
  | goto hbb hpc hend hdst htransfer =>
    rename_i bb pc e dst e'
    simp only [SInv] at hinv ⊢
    obtain ⟨hbb', hreach, hm⟩ := hinv
    have hlastfix : transferLast σ (cfg.blocks[bb]'hbb) = σ :=
      (block_fix hfix (b := ⟨bb, hbb⟩) hreach).2
    have hedge := taken_edge_fix hlastfix hm hend
    obtain ⟨hdr, hflow⟩ := transferEdge_fix hdst hedge
    obtain ⟨v', hv', rfl⟩ := Env.transfer_block_io_eq_some.mp htransfer
    exact ⟨hdst, hdr, hm.transfer_block_io hflow hv'⟩

/-! ### Step correspondence with the rewritten CFG -/

theorem rewriteCFG_size (cfg : ControlFlowGraph) (σ : AbsState cfg) :
    (rewriteCFG cfg σ).blocks.size = cfg.blocks.size :=
  size_rewriteBlocks cfg σ

theorem rewriteCFG_getElem {σ : AbsState cfg} {i : Nat} (h : i < cfg.blocks.size)
    (h' : i < (rewriteCFG cfg σ).blocks.size) :
    (rewriteCFG cfg σ).blocks[i]'h' = rewriteBlock σ (cfg.blocks[i]'h) :=
  getElem_rewriteBlocks cfg σ i h'

theorem stepOp_rewrite_iff {σ : AbsState cfg} {op : Op} {e e' : Env}
    (hopfix : transferOp σ op = σ) (hm : Models σ e.vars)
    (hrefs : ∀ r ∈ op.refs, (e.vars.get? r).isSome) :
    StepOp e (rewriteOp σ op) e' ↔ StepOp e op e' := by
  cases op with
  | const v w => exact Iff.rfl
  | persistentLoad out addr => exact Iff.rfl
  | persistentStore addr v => exact Iff.rfl
  | add32 r a b =>
    cases hg : σ.get r with
    | undef =>
      have hrw : rewriteOp σ (.add32 r a b) = .add32 r a b := by
        simp only [rewriteOp, hg]
      rw [hrw]
    | overdefined =>
      have hrw : rewriteOp σ (.add32 r a b) = .add32 r a b := by
        simp only [rewriteOp, hg]
      rw [hrw]
    | const w =>
      have hrw : rewriteOp σ (.add32 r a b) = .const r w := by
        simp only [rewriteOp, hg]
      rw [hrw]
      have key : ∀ x y, e.vars.get? a = some x → e.vars.get? b = some y → x + y = w := by
        intro x y hx hy
        have h1 : Value.const (x + y) ≤ σ.get r :=
          le_trans (Value.binop_sound (hm a x hx) (hm b y hy)) (join_fix hopfix)
        rw [hg] at h1
        exact Value.const_le_const h1
      constructor
      · intro h
        obtain rfl := Op.eval?_const_iff.mp h
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hrefs a (by simp [Op.refs]))
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hrefs b (by simp [Op.refs]))
        exact Op.eval?_add32_iff.mpr ⟨x, y, hx, hy, by rw [key x y hx hy]⟩
      · intro h
        obtain ⟨x, y, hx, hy, rfl⟩ := Op.eval?_add32_iff.mp h
        exact Op.eval?_const_iff.mpr (by rw [key x y hx hy])
  | lessThan r a b =>
    cases hg : σ.get r with
    | undef =>
      have hrw : rewriteOp σ (.lessThan r a b) = .lessThan r a b := by
        simp only [rewriteOp, hg]
      rw [hrw]
    | overdefined =>
      have hrw : rewriteOp σ (.lessThan r a b) = .lessThan r a b := by
        simp only [rewriteOp, hg]
      rw [hrw]
    | const w =>
      have hrw : rewriteOp σ (.lessThan r a b) = .const r w := by
        simp only [rewriteOp, hg]
      rw [hrw]
      have key : ∀ x y, e.vars.get? a = some x → e.vars.get? b = some y →
          (if x < y then (1 : Word) else 0) = w := by
        intro x y hx hy
        have h1 : Value.const (if x < y then 1 else 0) ≤ σ.get r :=
          le_trans (Value.binop_sound (f := fun x y => if x < y then 1 else 0)
            (hm a x hx) (hm b y hy)) (join_fix hopfix)
        rw [hg] at h1
        exact Value.const_le_const h1
      constructor
      · intro h
        obtain rfl := Op.eval?_const_iff.mp h
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hrefs a (by simp [Op.refs]))
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hrefs b (by simp [Op.refs]))
        exact Op.eval?_lessThan_iff.mpr ⟨x, y, hx, hy, by rw [key x y hx hy]⟩
      · intro h
        obtain ⟨x, y, hx, hy, rfl⟩ := Op.eval?_lessThan_iff.mp h
        exact Op.eval?_const_iff.mpr (by rw [key x y hx hy])

theorem stepEndOp_rewrite_iff {σ : AbsState cfg} {l : EndOp} {e : Env} {c : Continuation}
    (hm : Models σ e.vars)
    (hrefs : ∀ r ∈ l.var_refs, (e.vars.get? r).isSome) :
    StepEndOp e (rewriteLast σ l) c ↔ StepEndOp e l c := by
  cases l with
  | exit v => exact Iff.rfl
  | jump d => exact Iff.rfl
  | jump_if j =>
    cases hg : σ.get j.cond with
    | undef =>
      have hrw : rewriteLast σ (.jump_if j) = .jump_if j := by
        simp only [rewriteLast, hg]
      rw [hrw]
    | overdefined =>
      have hrw : rewriteLast σ (.jump_if j) = .jump_if j := by
        simp only [rewriteLast, hg]
      rw [hrw]
    | const w₀ =>
      have hrw : rewriteLast σ (.jump_if j)
          = .jump (if w₀ = 0 then j.dst_if_zero else j.dst_if_non_zero) := by
        simp only [rewriteLast, hg]
      rw [hrw]
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
        (hrefs j.cond (by simp [EndOp.var_refs]))
      obtain rfl : w = w₀ := by
        have h1 := hm j.cond w hw
        rw [hg] at h1
        exact Value.const_le_const h1
      constructor
      · intro h
        obtain rfl := EndOp.eval?_jump_iff.mp h
        exact EndOp.eval?_jump_if_iff.mpr ⟨w, hw, rfl⟩
      · intro h
        obtain ⟨w', hw', rfl⟩ := EndOp.eval?_jump_if_iff.mp h
        rw [hw] at hw'
        cases hw'
        exact EndOp.eval?_jump_iff.mpr rfl

theorem stepCFG_forward {σ : AbsState cfg} (hfix : step σ = σ) {c c' : Conf}
    (hinv : SInv cfg σ c) (hwf : WF cfg c) (hstep : StepCFG cfg c c') :
    StepCFG (rewriteCFG cfg σ) c c' := by
  cases hstep with
  | op hbb hpc hop =>
    rename_i bb pc e e'
    simp only [SInv] at hinv
    obtain ⟨hbb', hreach, hm⟩ := hinv
    have hbbR : bb < (rewriteCFG cfg σ).blocks.size := by
      rw [rewriteCFG_size]
      exact hbb
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    have hpcR : pc < ((rewriteCFG cfg σ).blocks[bb]'hbbR).ops.size := by
      rw [hblk, rewriteBlock_ops, Array.size_map]
      exact hpc
    refine StepCFG.op hbbR hpcR ?_
    have hopR : ((rewriteCFG cfg σ).blocks[bb]'hbbR).ops[pc]'hpcR
        = rewriteOp σ ((cfg.blocks[bb]'hbb).ops[pc]'hpc) := by
      simp only [hblk, rewriteBlock_ops, Array.getElem_map]
    rw [hopR]
    refine (stepOp_rewrite_iff ?_ hm (wf_op_refs hwf hbb hpc)).mpr hop
    exact (block_fix hfix (b := ⟨bb, hbb⟩) hreach).1 _ (Array.getElem_mem hpc)
  | exit hbb hpc hend =>
    rename_i bb pc e t
    simp only [SInv] at hinv
    obtain ⟨hbb', hreach, hm⟩ := hinv
    have hbbR : bb < (rewriteCFG cfg σ).blocks.size := by
      rw [rewriteCFG_size]
      exact hbb
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    refine StepCFG.exit hbbR ?_ ?_
    · rw [hblk, rewriteBlock_ops, Array.size_map]
      exact hpc
    · rw [hblk, rewriteBlock_last]
      exact (stepEndOp_rewrite_iff hm (wf_end_refs hwf hbb hpc)).mpr hend
  | goto hbb hpc hend hdst htransfer =>
    rename_i bb pc e dst e'
    simp only [SInv] at hinv
    obtain ⟨hbb', hreach, hm⟩ := hinv
    have hbbR : bb < (rewriteCFG cfg σ).blocks.size := by
      rw [rewriteCFG_size]
      exact hbb
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    have hdstR : dst.idx < (rewriteCFG cfg σ).blocks.size := by
      rw [rewriteCFG_size]
      exact hdst
    have hdblk := rewriteCFG_getElem (σ := σ) hdst hdstR
    refine StepCFG.goto hbbR ?_ ?_ hdstR ?_
    · rw [hblk, rewriteBlock_ops, Array.size_map]
      exact hpc
    · rw [hblk, rewriteBlock_last]
      exact (stepEndOp_rewrite_iff hm (wf_end_refs hwf hbb hpc)).mpr hend
    · rw [hblk, hdblk, rewriteBlock_outputs, rewriteBlock_inputs]
      exact htransfer

theorem stepCFG_backward {σ : AbsState cfg} (hfix : step σ = σ) {c c' : Conf}
    (hinv : SInv cfg σ c) (hwf : WF cfg c) (hstep : StepCFG (rewriteCFG cfg σ) c c') :
    StepCFG cfg c c' := by
  cases hstep with
  | op hbbR hpcR hop =>
    rename_i bb pc e e'
    simp only [SInv] at hinv
    obtain ⟨hbb, hreach, hm⟩ := hinv
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    have hpc : pc < (cfg.blocks[bb]'hbb).ops.size := by
      have h := hpcR
      rw [hblk, rewriteBlock_ops, Array.size_map] at h
      exact h
    refine StepCFG.op hbb hpc ?_
    have hopR : ((rewriteCFG cfg σ).blocks[bb]'hbbR).ops[pc]'hpcR
        = rewriteOp σ ((cfg.blocks[bb]'hbb).ops[pc]'hpc) := by
      simp only [hblk, rewriteBlock_ops, Array.getElem_map]
    rw [hopR] at hop
    refine (stepOp_rewrite_iff ?_ hm (wf_op_refs hwf hbb hpc)).mp hop
    exact (block_fix hfix (b := ⟨bb, hbb⟩) hreach).1 _ (Array.getElem_mem hpc)
  | exit hbbR hpcR hend =>
    rename_i bb pc e t
    simp only [SInv] at hinv
    obtain ⟨hbb, hreach, hm⟩ := hinv
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    have hpc : pc = (cfg.blocks[bb]'hbb).ops.size := by
      have h := hpcR
      rw [hblk, rewriteBlock_ops, Array.size_map] at h
      exact h
    refine StepCFG.exit hbb hpc ?_
    rw [hblk, rewriteBlock_last] at hend
    exact (stepEndOp_rewrite_iff hm (wf_end_refs hwf hbb hpc)).mp hend
  | goto hbbR hpcR hend hdstR htransfer =>
    rename_i bb pc e dst e'
    simp only [SInv] at hinv
    obtain ⟨hbb, hreach, hm⟩ := hinv
    have hblk := rewriteCFG_getElem (σ := σ) hbb hbbR
    have hdst : dst.idx < cfg.blocks.size := by
      rw [rewriteCFG_size] at hdstR
      exact hdstR
    have hdblk := rewriteCFG_getElem (σ := σ) hdst hdstR
    have hpc : pc = (cfg.blocks[bb]'hbb).ops.size := by
      have h := hpcR
      rw [hblk, rewriteBlock_ops, Array.size_map] at h
      exact h
    refine StepCFG.goto hbb hpc ?_ hdst ?_
    · rw [hblk, rewriteBlock_last] at hend
      exact (stepEndOp_rewrite_iff hm (wf_end_refs hwf hbb hpc)).mp hend
    · rw [hblk, hdblk, rewriteBlock_outputs, rewriteBlock_inputs] at htransfer
      exact htransfer

/-! ### Trace transport and the preservation theorem -/

theorem _root_.Sir.preservesSemantics_iff {f : SSACFG → SSACFG} :
    PreservesSemantics f ↔
      ∀ (cfg : SSACFG) (w : World) (t : Termination) (w' : World),
        ((∃ fuel, (f cfg).val.eval? w fuel = .ok (t, w')) ↔
          ∃ fuel, cfg.val.eval? w fuel = .ok (t, w')) :=
  Iff.rfl

theorem steps_forward {σ : AbsState cfg} (hfix : step σ = σ) {c c' : Conf}
    (hsteps : CFGSteps cfg c c') :
    SInv cfg σ c → WF cfg c → CFGSteps (rewriteCFG cfg σ) c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ _ => .refl
  | head hstep _ ih =>
    intro hinv hwf
    exact Relation.ReflTransGen.head (stepCFG_forward hfix hinv hwf hstep)
      (ih (sinv_step hfix hstep hinv) (wf_step hstep hwf))

theorem steps_backward {σ : AbsState cfg} (hfix : step σ = σ) {c c' : Conf}
    (hsteps : CFGSteps (rewriteCFG cfg σ) c c') :
    SInv cfg σ c → WF cfg c → CFGSteps cfg c c' := by
  induction hsteps using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ _ => .refl
  | head hstep _ ih =>
    intro hinv hwf
    have horig := stepCFG_backward hfix hinv hwf hstep
    exact Relation.ReflTransGen.head horig
      (ih (sinv_step hfix horig hinv) (wf_step horig hwf))

theorem run_sccp_preserves.proof : PreservesSemantics run_sccp := by
  rw [preservesSemantics_iff]
  intro cfg w t w'
  rw [ControlFlowGraph.eval?_iff_steps.proof, ControlFlowGraph.eval?_iff_steps.proof]
  have hfix : step (analyze cfg.val) = analyze cfg.val := step_analyze cfg.val
  have hinv : SInv cfg.val (analyze cfg.val) (cfg.val.initialConf w) :=
    sinv_init (analyze_entry_reachable cfg.val) w
  have hwf := wf_init cfg.val w
  have hconf : (run_sccp cfg).val.initialConf w = cfg.val.initialConf w := rfl
  constructor
  · intro h
    rw [hconf] at h
    exact steps_backward hfix h hinv hwf
  · intro h
    rw [hconf]
    exact steps_forward hfix h hinv hwf

end SCCP

end Sir
