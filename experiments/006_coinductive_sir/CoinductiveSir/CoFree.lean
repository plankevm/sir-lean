inductive CoStep (Effect : Type → Type) (Res State : Type) : Type 1 where
  | pure (value : Res)
  | silent (next : State)
  | impure {X : Type} (operation : Effect X) (next : X → State)

structure CoFree (Effect : Type → Type) (Res : Type) : Type 1 where
  State : Type
  initial : State
  observe : State → CoStep Effect Res State

def CoFree.pure (value : A) : CoFree E A := ⟨Unit, (), fun _ => .pure value⟩

def CoFree.perform (operation : E X) : CoFree E X where
  State := Option X
  initial := none
  observe
  | none => .impure operation some
  | some res => .pure res

private inductive BindState (Source : Type) (next : A → CoFree E B) where
  | source (state : Source)
  | target (value : A) (state : (next value).State)

def CoFree.bind (program : CoFree E A) (next : A → CoFree E B) : CoFree E B where
  State := BindState program.State next
  initial := .source program.initial
  observe
  | .source state =>
      match program.observe state with
      | .pure value => .silent (.target value (next value).initial)
      | .silent next => .silent (.source next)
      | .impure operation continueWith => .impure operation (.source ∘ continueWith)
  | .target value state =>
      match (next value).observe state with
      | .pure value => .pure value
      | .silent next => .silent (.target value next)
      | .impure operation continueWith => .impure operation (.target value ∘ continueWith)

def CoFree.map (f : A → B) (program : CoFree E A) : CoFree E B where
  State := program.State
  initial := program.initial
  observe state :=
    match program.observe state with
    | .pure value => .pure (f value)
    | .silent next => .silent next
    | .impure operation resume => .impure operation resume

instance : Functor (CoFree E) where
  map := CoFree.map

instance : Pure (CoFree E) where
  pure := CoFree.pure

instance : Monad (CoFree E) where
  bind := CoFree.bind


inductive IterStep (S E : Type) where
  | repeat : S → IterStep S E
  | exit : E → IterStep S E

private structure IterState (next : S → CoFree E (IterStep S A)) where
  index : S
  state : (next index).State

def CoFree.iter (start : S) (next : S → CoFree E (IterStep S A)) : CoFree E A where
  State := IterState next
  initial := ⟨start, (next start).initial⟩
  observe control :=
    match (next control.index).observe control.state with
    | .pure (.repeat index) => .silent ⟨index, (next index).initial⟩
    | .pure (.exit value) => .pure value
    | .silent state => .silent ⟨control.index, state⟩
    | .impure operation resume => .impure operation (fun answer => ⟨control.index, resume answer⟩)

def CoFree.iterExcept (start : S)
    (next : S → ExceptT ε (CoFree E) (IterStep S A)) : ExceptT ε (CoFree E) A :=
  ExceptT.mk <| CoFree.iter start fun state =>
    Functor.map
      (fun
       | .ok (.repeat state) => .repeat state
       | .ok (.exit value) => .exit (.ok value)
       | .error error => .exit (.error error))
      (ExceptT.run (next state))

instance : ForIn (CoFree E) Lean.Loop Unit where
  forIn _ initial body :=
    CoFree.iter initial fun state => (body () state).map
      (fun
       | .yield state' => .repeat state'
       | .done state'  => .exit state')

inductive EffectSum (L R : Type → Type) : Type → Type where
  | inl {X} : L X → EffectSum L R X
  | inr {X} : R X → EffectSum L R X

inductive Recur (Inp Out : Type) : Type → Type where
  | call (args : Inp) : Recur Inp Out Out

infixr:65 " ⊕ₑ " => EffectSum

structure FixFrame (body : Inp → CoFree (Recur Inp Out ⊕ₑ E) Out) : Type where
  caller : Inp
  resume : Out → (body caller).State

private structure FixState (body : Inp → CoFree (Recur Inp Out ⊕ₑ E) Out) where
  input : Inp
  innerState : (body input).State
  stack : List (FixFrame body)

def CoFree.fix
    (f : (Inp → CoFree (Recur Inp Out ⊕ₑ E) Out) → (Inp → CoFree (Recur Inp Out ⊕ₑ E) Out)) :
    Inp → CoFree E Out :=
  let body := f (fun input => CoFree.perform (.inl (.call input)))
  fun input => {
    State := FixState body
    initial := ⟨input, (body input).initial, []⟩
    observe control :=
      match (body control.input).observe control.innerState, control.stack with
      | .pure value, [] => .pure value
      | .pure value, ⟨caller, resume⟩ :: rest => .silent ⟨caller, resume value, rest⟩
      | .silent state, stack => .silent ⟨control.input, state, stack⟩
      | .impure (.inl (.call input)) resume, stack => .silent ⟨input, (body input).initial, ⟨control.input, resume⟩ :: stack⟩
      | .impure (.inr operation) resume, stack => .impure operation (fun x => ⟨control.input, resume x, stack⟩)
  }

