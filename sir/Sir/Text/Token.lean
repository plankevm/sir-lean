import Sir.Vars.Spec

namespace Sir.Vars.Text

inductive Token where
  | identifier (name : String)
  | label (name : String)
  | number (value : Nat)
  | equals
  | arrow
  | fatArrow
  | colon
  | question
  | leftBrace
  | rightBrace
  | newline
  | invalid (character : Char)
deriving DecidableEq, Repr, Inhabited

def isIdentifierBody (character : Char) : Bool :=
  character.isAlphanum || character == '_'

def isHexDigit (character : Char) : Bool :=
  character.isDigit || ('a' ≤ character && character ≤ 'f') ||
    ('A' ≤ character && character ≤ 'F')

def digitValue (character : Char) : Nat :=
  if character.isDigit then character.toNat - '0'.toNat
  else if character ≤ 'F' then character.toNat - 'A'.toNat + 10
  else character.toNat - 'a'.toNat + 10

def digitsValue (base : Nat) (digits : List Char) : Nat :=
  digits.foldl (fun value digit => value * base + digitValue digit) 0

def decimalDigitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def decimalDigitsAux : Nat → Nat → List Char
  | 0, value => [decimalDigitChar value]
  | fuel + 1, value =>
      if value < 10 then [decimalDigitChar value]
      else decimalDigitsAux fuel (value / 10) ++ [decimalDigitChar (value % 10)]

def decimalDigits (value : Nat) : List Char :=
  decimalDigitsAux value value

def decimalString (value : Nat) : String :=
  String.ofList (decimalDigits value)

inductive Pending where
  | idle
  | word (characters : List Char)
  | label (characters : List Char)
  | lineComment
  | blockComment
  | blockCommentStar

def wordToken : List Char → Token
  | '0' :: 'x' :: digits =>
      if digits.isEmpty || !digits.all isHexDigit then .invalid '0'
      else .number (digitsValue 16 digits)
  | first :: rest =>
      if first.isDigit then
        if (first :: rest).all Char.isDigit then .number (digitsValue 10 (first :: rest))
        else .invalid first
      else .identifier (String.ofList (first :: rest))
  | [] => .invalid ' '

def flush : Pending → List Token
  | .word characters => [wordToken characters.reverse]
  | .label [] => [.invalid '@']
  | .label characters => [.label (String.ofList characters.reverse)]
  | _ => []

def separatorTokens : Char → List Token
  | '@' => []
  | '=' => [.equals]
  | ':' => [.colon]
  | '?' => [.question]
  | '{' => [.leftBrace]
  | '}' => [.rightBrace]
  | '\n' => [.newline]
  | ' ' | '\t' | '\r' => []
  | character => [.invalid character]

def tokenizeAux : Pending → List Char → List Token
  | pending, [] => flush pending
  | .lineComment, '\n' :: rest => .newline :: tokenizeAux .idle rest
  | .lineComment, _ :: rest => tokenizeAux .lineComment rest
  | .blockComment, '*' :: rest => tokenizeAux .blockCommentStar rest
  | .blockComment, '\n' :: rest => .newline :: tokenizeAux .blockComment rest
  | .blockComment, _ :: rest => tokenizeAux .blockComment rest
  | .blockCommentStar, '/' :: rest => tokenizeAux .idle rest
  | .blockCommentStar, '*' :: rest => tokenizeAux .blockCommentStar rest
  | .blockCommentStar, '\n' :: rest => .newline :: tokenizeAux .blockComment rest
  | .blockCommentStar, _ :: rest => tokenizeAux .blockComment rest
  | pending, '/' :: '/' :: rest => flush pending ++ tokenizeAux .lineComment rest
  | pending, '/' :: '*' :: rest => flush pending ++ tokenizeAux .blockComment rest
  | pending, '-' :: '>' :: rest => flush pending ++ .arrow :: tokenizeAux .idle rest
  | pending, '=' :: '>' :: rest => flush pending ++ .fatArrow :: tokenizeAux .idle rest
  | pending, character :: rest =>
      if isIdentifierBody character then
        match pending with
        | .word characters => tokenizeAux (.word (character :: characters)) rest
        | .label characters => tokenizeAux (.label (character :: characters)) rest
        | _ => tokenizeAux (.word [character]) rest
      else
        flush pending ++ separatorTokens character ++
          tokenizeAux (if character == '@' then .label [] else .idle) rest

def tokenize (source : String) : List Token :=
  tokenizeAux .idle source.toList

def Token.characters : Token → List Char
  | .identifier name => name.toList
  | .label name => '@' :: name.toList
  | .number value => decimalDigits value
  | .equals => ['=']
  | .arrow => ['-', '>']
  | .fatArrow => ['=', '>']
  | .colon => [':']
  | .question => ['?']
  | .leftBrace => ['{']
  | .rightBrace => ['}']
  | .newline => ['\n']
  | .invalid character => [character]

def renderChars : List Token → List Char
  | [] => []
  | .newline :: rest => '\n' :: renderChars rest
  | token :: rest => token.characters ++ ' ' :: renderChars rest

def render (tokens : List Token) : String :=
  String.ofList (renderChars tokens)

end Sir.Vars.Text
