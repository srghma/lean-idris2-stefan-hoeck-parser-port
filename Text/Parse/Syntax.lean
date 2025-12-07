import Text.Parse.Manual

universe u

namespace Text.Parse.Syntax

open Text.Parse.Manual
open Data.List.Suffix

@[inline]
def pure {t e a} (v : a) : Grammar false t e a :=
  fun ts => Result0.Succ0 v ts Suffix.Same

def orElse {b1 b2 t e a} (g1 : Grammar b1 t e a) (g2 : Thunk (Grammar b2 t e a)) : Grammar (b1 && b2) t e a :=
  fun ts =>
    match g1 ts with
    | res@(Result0.Succ0 ..) => and1 res
    | Result0.Fail0 _ => and2 (g2.get ts)

infixl:30 " <|> " => orElse

@[inline]
def ap {b1 b2 t e a b} (gf : Grammar b1 t e (a → b)) (ga : Grammar b2 t e a) : Grammar (b1 || b2) t e b :=
  fun ts =>
    match gf ts with
    | Result0.Succ0 f r1 p =>
      match ga r1 with
      | Result0.Succ0 v r2 q => Result0.Succ0 (f v) r2 (q.trans p)
      | Result0.Fail0 err => Result0.Fail0 err
    | Result0.Fail0 err => Result0.Fail0 err

@[inline]
def seqRight {b1 b2 t e a} (g1 : Grammar b1 t e Unit) (g2 : Grammar b2 t e a) : Grammar (b1 || b2) t e a :=
  ap (ap (pure (fun _ x => x)) g1) g2

@[inline]
def seqLeft {b1 b2 t e a} (g1 : Grammar b1 t e a) (g2 : Grammar b2 t e Unit) : Grammar (b1 || b2) t e a :=
  ap (ap (pure (fun x _ => x)) g1) g2

partial def many {t e a} (g : Grammar true t e a) : Grammar false t e (List a) :=
  let rec go (acc : List a) (ts : List (Bounded t)) : Res false t ts e (List a) :=
    match g ts with
    | Result0.Succ0 v rem p =>
      -- Recurse, but since we are not proving termination, we must be careful
      -- to consume input to avoid infinite loops. The `strict` annotation on `g`
      -- helps with this, but is not a formal guarantee.
      go (v :: acc) rem
    | Result0.Fail0 _ => Result0.Succ0 acc.reverse ts Suffix.Same
  fun ts => go [] ts

def optional {t e a b} (g : Grammar b t e a) : Grammar false t e (Option a) :=
  let g' : Grammar b t e (Option a) := fun ts =>
    match g ts with
    | Result0.Succ0 v rem p => Result0.Succ0 (some v) rem p
    | Result0.Fail0 err => Result0.Fail0 err
  orElse (weaken g') (fun _ => pure none)


end Text.Parse.Syntax
