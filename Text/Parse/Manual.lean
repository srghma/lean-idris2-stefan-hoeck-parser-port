import Data.List.Suffix.Result0
import Text.Lex.Manual -- For Bounded, InnerError, etc.

universe u

namespace Text.Parse.Manual

open Text.Lex.Manual
open Data.List.Suffix

abbrev Res (b : Bool) (t : Type u) (ts : List (Bounded t)) (e a : Type u) :=
  Result0 ts b (α := a) (ε := (Bounded (InnerError e)))

abbrev Grammar (strict : Bool) (t e a : Type u) :=
  (ts : List (Bounded t)) → Res strict t ts e a

-- Dummy Error Helpers
-- These are placeholders to allow the grammar functions to be compiled.
-- A full implementation would create more meaningful error messages.
def eoi {t e a b ts} : Res b t ts e a := Result0.Fail0 (default : Bounded (InnerError e))
def unexpected {t e a b ts} (tok : Bounded t) : Res b t ts e a := Result0.Fail0 (default)
def expected {t e a b ts} (bds: Bounds) (exp: t) (act: String) : Res b t ts e a := Result0.Fail0 (default)
def custom {t e a b ts} (bds: Bounds) (err: e) : Res b t ts e a := Result0.Fail0 (default)

-- Conversions
@[inline] unsafe def swapOr {t e a x y} (g : Grammar (x || y) t e a) : Grammar (y || x) t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def orSame {t e a x} (g : Grammar (x || x) t e a) : Grammar x t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def orTrue {t e a x} (g : Grammar (x || true) t e a) : Grammar true t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def orFalse {t e a x} (g : Grammar (x || false) t e a) : Grammar x t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def swapAnd {t e a x y} (g : Grammar (x && y) t e a) : Grammar (y && x) t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def andSame {t e a x} (g : Grammar (x && x) t e a) : Grammar x t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def andTrue {t e a x} (g : Grammar (x && true) t e a) : Grammar x t e a := fun ts => unsafeCast (g ts)
@[inline] unsafe def andFalse {t e a x} (g : Grammar (x && false) t e a) : Grammar false t e a := fun ts => unsafeCast (g ts)

-- Simple Grammars
def terminal {t e a} [ToString t] (f : t → Option a) : Grammar true t e a
  | B v b :: xs =>
    match f v with
    | some r => Result0.Succ0 r xs (Suffix.Uncons Suffix.Same)
    | none => unexpected (B v b)
  | [] => eoi

def terminalE {t e a} (f : t → Except e a) : Grammar true t e a
  | B v b :: xs =>
    match f v with
    | Except.ok r => Result0.Succ0 r xs (Suffix.Uncons Suffix.Same)
    | Except.error err => custom b err
  | [] => eoi

def exact {t e} [ToString t] [BEq t] (v : t) : Grammar true t e Unit
  | x :: xs =>
    if v == x.val
    then Result0.Succ0 () xs (Suffix.Uncons Suffix.Same)
    else expected x.bounds v s!"{x.val}"
  | [] => expected default v ""

def peek {t e} : Grammar false t e t
  | x :: xs => Result0.Succ0 x.val (x :: xs) Suffix.Same
  | [] => eoi

def nextIs {t e} [ToString t] (f : t → Bool) : Grammar false t e t
  | x :: xs =>
    if f x.val
    then Result0.Succ0 x.val (x :: xs) Suffix.Same
    else unexpected x
  | [] => eoi

def nextEquals {t e} [ToString t] [BEq t] (v : t) : Grammar false t e t
  | x :: xs =>
    if v == x.val
    then Result0.Succ0 x.val (x :: xs) Suffix.Same
    else expected x.bounds v s!"{x.val}"
  | [] => expected default v ""

end Text.Parse.Manual
