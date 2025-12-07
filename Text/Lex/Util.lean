import Text.Lex.Core
import Text.Lex.Shift
import Text.Lex.Manual

universe u

namespace Text.Lex.Util

open Text.Lex
open Data.List

-- List/SnocList Utilities

def stripQuotes (sl : SnocList Char) : String :=
  match sl.toList with
  | _ :: t => String.mk (t.dropLast)
  | [] => ""

namespace List
  def ltrim : List Char → List Char
  | c :: cs => if c.isWhitespace then ltrim cs else c :: cs
  | [] => []
end List

namespace SnocList
  def rtrim (sl : SnocList Char) : SnocList Char :=
    (sl.toList.reverse.ltrim).reverse
end SnocList

-- Helper for creating lexers from shifters
@[inline]
def autoLift {s} (f : AutoShift s) : Recognise s :=
  Recognise.Lift (fun st ts => unsafeCast (f ts (Data.List.Shift.Same)))

-- Single-Character Lexers

@[inline]
def any : Lexer := autoLift (one (fun _ => true))

@[inline]
def pred (f : Char → Bool) : Lexer := autoLift (one f)

@[inline] def is (c : Char) : Lexer := pred (· == c)
@[inline] def isNot (c : Char) : Lexer := pred (· != c)
@[inline] def space : Lexer := pred Char.isWhitespace
@[inline] def digit : Lexer := pred Char.isDigit

@[inline]
def like (c : Char) : Lexer :=
  let upper_c := c.toUpper
  pred (fun x => x.toUpper == upper_c)

@[inline]
def oneOf (cs : List Char) : Lexer := pred (fun c => cs.elem c)

@[inline]
def range (start end' : Char) : Lexer :=
  let s := min start end'
  let e := max start end'
  pred (fun c => c >= s && c <= e)

-- Multi-Character Lexers

def exact (s : String) : Lexer :=
  let rec go : List Char → Lexer
    | [c] => is c
    | c :: cs => is c <+> go cs
    | [] => fail
  if s.isEmpty then fail else go s.toList

@[inline]
def preds (f : Char → Bool) : Lexer := autoLift (takeWhile1 f)

@[inline]
def spaces : Lexer := preds Char.isWhitespace

def newline : Lexer :=
  Recognise.Lift fun sc cs =>
    match cs with
    | '\r' :: '\n' :: t => pure (ShiftRes.Succ t default)
    | '\n' :: t => pure (ShiftRes.Succ t default)
    | '\r' :: t => pure (ShiftRes.Succ t default)
    | _ => fail sc cs

def manyTillNewline : Recognise false :=
  opt <| preds (fun | '\n' | '\r' => false | _ => true)

@[inline]
def lineComment (pre : Lexer) : Lexer :=
  pre <+> manyTillNewline

-- Combinators

def manyUntil (stopBefore : Recognise c) (l : Lexer) : Recognise false :=
  many (reject stopBefore <+> l)

def surround (start end' l : Lexer) : Lexer :=
  start <+> many (reject end' <+> l) <+> end'

@[inline] def quote (q l : Lexer) : Lexer := surround q q l
@[inline] def escape (esc l : Lexer) : Lexer := esc <+> l

-- Literals

@[inline]
def stringLit : Lexer := Recognise.Lift string

@[inline]
def intLit : Lexer := autoLift (takeWhile1 Char.isDigit)

def charLit : Lexer :=
  let q := is '\''
  q <+> (escape (is '\\') any <|> isNot '\'') <+> q

end Text.Lex.Util
