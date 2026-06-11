import SirLean.IR
import SirLean.State
import SirLean.SmallStep
import SirLean.Eval

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

end Sir
