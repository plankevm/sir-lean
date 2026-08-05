import Sir.Text.Token

namespace Sir.Vars.Text

theorem digitValue_decimalDigitChar {value : Nat} (h : value < 10) :
    digitValue (decimalDigitChar value) = value := by
  match value, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | _ + 10, h => omega

theorem digitsValue_append_singleton (base : Nat) (digits : List Char) (digit : Char) :
    digitsValue base (digits ++ [digit]) = digitsValue base digits * base + digitValue digit := by
  simp [digitsValue, List.foldl_append]

theorem digitsValue_decimalDigitsAux : ∀ (fuel value : Nat), value ≤ fuel →
    digitsValue 10 (decimalDigitsAux fuel value) = value
  | 0, value, h => by
      have : value = 0 := Nat.le_zero.mp h
      subst this
      rfl
  | fuel + 1, value, h => by
      rw [decimalDigitsAux]
      by_cases hsmall : value < 10
      · rw [if_pos hsmall]
        simpa [digitsValue] using digitValue_decimalDigitChar hsmall
      · have hten : 10 ≤ value := Nat.le_of_not_lt hsmall
        have hlt : value / 10 < value := Nat.div_lt_self (by omega) (by omega)
        have hrec := digitsValue_decimalDigitsAux fuel (value / 10) (by omega)
        rw [if_neg hsmall, digitsValue_append_singleton, hrec,
          digitValue_decimalDigitChar (Nat.mod_lt _ (by omega))]
        omega

theorem digitsValue_decimalDigits (value : Nat) :
    digitsValue 10 (decimalDigits value) = value :=
  digitsValue_decimalDigitsAux value value (Nat.le_refl value)

theorem decimalDigitChar_isDigit (value : Nat) : (decimalDigitChar value).isDigit = true := by
  match value with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | _ + 9 => rfl

theorem decimalDigitsAux_ne_nil : ∀ (fuel value : Nat), decimalDigitsAux fuel value ≠ []
  | 0, _ => by simp [decimalDigitsAux]
  | fuel + 1, value => by
      rw [decimalDigitsAux]
      by_cases hsmall : value < 10
      · rw [if_pos hsmall]; simp
      · rw [if_neg hsmall]; simp

theorem decimalDigitsAux_all_isDigit : ∀ (fuel value : Nat),
    (decimalDigitsAux fuel value).all Char.isDigit = true
  | 0, value => by simp [decimalDigitsAux, decimalDigitChar_isDigit]
  | fuel + 1, value => by
      rw [decimalDigitsAux]
      by_cases hsmall : value < 10
      · rw [if_pos hsmall]; simp [decimalDigitChar_isDigit]
      · rw [if_neg hsmall]
        simp [decimalDigitsAux_all_isDigit fuel, decimalDigitChar_isDigit]

theorem decimalDigits_ne_nil (value : Nat) : decimalDigits value ≠ [] :=
  decimalDigitsAux_ne_nil value value

theorem decimalDigits_all_isDigit (value : Nat) :
    (decimalDigits value).all Char.isDigit = true :=
  decimalDigitsAux_all_isDigit value value

theorem isIdentifierBody_of_isDigit {character : Char} (h : character.isDigit = true) :
    isIdentifierBody character = true := by
  simp [isIdentifierBody, Char.isAlphanum, h]

theorem tokenizeAux_idle_newline (characters : List Char) :
    tokenizeAux .idle ('\n' :: characters) = .newline :: tokenizeAux .idle characters := rfl

theorem tokenizeAux_idle_at (characters : List Char) :
    tokenizeAux .idle ('@' :: characters) = tokenizeAux (.label []) characters := rfl

theorem tokenizeAux_word_space (accumulator characters : List Char) :
    tokenizeAux (.word accumulator) (' ' :: characters) =
      wordToken accumulator.reverse :: tokenizeAux .idle characters := rfl

theorem tokenizeAux_label_space (accumulator characters : List Char) :
    tokenizeAux (.label accumulator) (' ' :: characters) =
      flush (.label accumulator) ++ tokenizeAux .idle characters := by
  cases accumulator <;> rfl

theorem tokenizeAux_idle_body {character : Char} (h : isIdentifierBody character = true)
    (characters : List Char) :
    tokenizeAux .idle (character :: characters) = tokenizeAux (.word [character]) characters := by
  rw [tokenizeAux.eq_def]
  split <;> simp_all <;> exact absurd h (by decide)

theorem tokenizeAux_word_body {character : Char} (h : isIdentifierBody character = true)
    (accumulator characters : List Char) :
    tokenizeAux (.word accumulator) (character :: characters) =
      tokenizeAux (.word (character :: accumulator)) characters := by
  rw [tokenizeAux.eq_def]
  split <;> simp_all <;> exact absurd h (by decide)

theorem tokenizeAux_label_body {character : Char} (h : isIdentifierBody character = true)
    (accumulator characters : List Char) :
    tokenizeAux (.label accumulator) (character :: characters) =
      tokenizeAux (.label (character :: accumulator)) characters := by
  rw [tokenizeAux.eq_def]
  split <;> simp_all <;> exact absurd h (by decide)

theorem tokenizeAux_word_run : ∀ (word : List Char), word.all isIdentifierBody = true →
    ∀ (accumulator characters : List Char),
      tokenizeAux (.word accumulator) (word ++ ' ' :: characters) =
        wordToken (accumulator.reverse ++ word) :: tokenizeAux .idle characters
  | [], _, accumulator, characters => by simp [tokenizeAux_word_space]
  | first :: rest, h, accumulator, characters => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [List.cons_append, tokenizeAux_word_body h.left,
        tokenizeAux_word_run rest h.right]
      simp

theorem tokenizeAux_label_run : ∀ (word : List Char), word.all isIdentifierBody = true →
    ∀ (accumulator characters : List Char),
      tokenizeAux (.label accumulator) (word ++ ' ' :: characters) =
        flush (.label (word.reverse ++ accumulator)) ++ tokenizeAux .idle characters
  | [], _, accumulator, characters => by simp [tokenizeAux_label_space]
  | first :: rest, h, accumulator, characters => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      rw [List.cons_append, tokenizeAux_label_body h.left,
        tokenizeAux_label_run rest h.right]
      simp

theorem flush_label_of_ne_nil {characters : List Char} (h : characters ≠ []) :
    flush (.label characters) = [.label (String.ofList characters.reverse)] := by
  cases characters with
  | nil => exact absurd rfl h
  | cons first rest => rfl

theorem wordToken_identifier {first : Char} {rest : List Char} (h : first.isDigit = false) :
    wordToken (first :: rest) = .identifier (String.ofList (first :: rest)) := by
  rw [wordToken.eq_def]
  split <;> simp_all

theorem wordToken_number {characters : List Char} (hne : characters ≠ [])
    (h : characters.all Char.isDigit = true) :
    wordToken characters = .number (digitsValue 10 characters) := by
  rw [wordToken.eq_def]
  split <;> simp_all

theorem all_isIdentifierBody_of_all_isDigit : ∀ {characters : List Char},
    characters.all Char.isDigit = true → characters.all isIdentifierBody = true
  | [], _ => rfl
  | _ :: rest, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h ⊢
      exact ⟨isIdentifierBody_of_isDigit h.left, all_isIdentifierBody_of_all_isDigit h.right⟩

def Token.Renderable : Token → Prop
  | .identifier name =>
      ∃ first rest, name.toList = first :: rest ∧ first.isDigit = false ∧
        (first :: rest).all isIdentifierBody = true
  | .label name =>
      ∃ first rest, name.toList = first :: rest ∧ (first :: rest).all isIdentifierBody = true
  | .invalid _ => False
  | _ => True

theorem tokenizeAux_idle_characters {token : Token} (h : token.Renderable)
    (characters : List Char) :
    tokenizeAux .idle (token.characters ++ ' ' :: characters) =
      token :: tokenizeAux .idle characters := by
  cases token with
  | identifier name =>
      obtain ⟨first, rest, hname, hdigit, hbody⟩ := h
      simp only [List.all_cons, Bool.and_eq_true] at hbody
      show tokenizeAux .idle (name.toList ++ ' ' :: characters) = _
      rw [hname, List.cons_append, tokenizeAux_idle_body hbody.left,
        tokenizeAux_word_run rest hbody.right]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [wordToken_identifier hdigit, ← hname, String.ofList_toList]
  | label name =>
      obtain ⟨first, rest, hname, hbody⟩ := h
      show tokenizeAux .idle ('@' :: name.toList ++ ' ' :: characters) = _
      rw [List.cons_append, tokenizeAux_idle_at, hname,
        tokenizeAux_label_run _ hbody, List.append_nil,
        flush_label_of_ne_nil (by simp), List.reverse_reverse, ← hname,
        String.ofList_toList]
      rfl
  | number value =>
      obtain ⟨first, rest, hdigits⟩ := List.exists_cons_of_ne_nil (decimalDigits_ne_nil value)
      have hall := decimalDigits_all_isDigit value
      have hbody := all_isIdentifierBody_of_all_isDigit hall
      rw [hdigits] at hbody
      simp only [List.all_cons, Bool.and_eq_true] at hbody
      show tokenizeAux .idle (decimalDigits value ++ ' ' :: characters) = _
      rw [hdigits, List.cons_append, tokenizeAux_idle_body hbody.left,
        tokenizeAux_word_run rest hbody.right]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      rw [← hdigits, wordToken_number (decimalDigits_ne_nil value) hall,
        digitsValue_decimalDigits]
  | invalid character => exact h.elim
  | _ => rfl

theorem renderChars_cons {token : Token} (h : token ≠ .newline) (tokens : List Token) :
    renderChars (token :: tokens) = token.characters ++ ' ' :: renderChars tokens := by
  cases token <;> first | rfl | exact absurd rfl h

theorem tokenizeAux_idle_renderChars : ∀ (tokens : List Token),
    (∀ token ∈ tokens, token.Renderable) → tokenizeAux .idle (renderChars tokens) = tokens := by
  intro tokens
  induction tokens with
  | nil => intro _; rfl
  | cons token rest ih =>
      intro h
      have hrest : ∀ t ∈ rest, t.Renderable := fun t ht => h t (List.mem_cons_of_mem _ ht)
      have htoken : token.Renderable := h token (by simp)
      by_cases hnewline : token = .newline
      · subst hnewline
        rw [show renderChars (Token.newline :: rest) = '\n' :: renderChars rest from rfl,
          tokenizeAux_idle_newline, ih hrest]
      · rw [renderChars_cons hnewline, tokenizeAux_idle_characters htoken, ih hrest]

theorem tokenize_render {tokens : List Token} (h : ∀ token ∈ tokens, token.Renderable) :
    tokenize (render tokens) = tokens := by
  simp only [tokenize, render, String.toList_ofList]
  exact tokenizeAux_idle_renderChars tokens h

end Sir.Vars.Text
