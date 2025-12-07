import Data.List.Suffix
import Data.Bool.Rewrite

universe u

namespace Data.List.Suffix

/--
  Result of consuming and converting a (possibly strict) prefix of a list of tokens.

  This comes with a proof about the number of tokens consumed.

  - strict: `true` if a strict prefix of the list of tokens has been consumed.
  - t:      The type of token consumed.
  - ts:     The original list of tokens.
  - e:      The error type in case of a failure.
  - a:      The result type.
-/
inductive Result0 {t e a : Type u} (ts : List t) : Bool → Type u where
  | Succ0 {b : Bool} (val : a) (xs : List t) (p : Suffix b xs ts) : Result0 ts b
  | Fail0 {b : Bool} (err : e) : Result0 ts b

/-- Alias for `Succ0`, which takes the proof as an explicit argument. -/
@[inline]
def succ {t e a : Type u} {ts : List t} {b : Bool} (val : a) {xs : List t}
  (p : Suffix b xs ts) : Result0 ts b :=
  Result0.Succ0 val xs p

instance {t e : Type u} {ts : List t} {b : Bool} : Functor (Result0 ts b) where
  map f
    | Result0.Succ0 v xs p => Result0.Succ0 (f v) xs p
    | Result0.Fail0 err => Result0.Fail0 err

@[inline]
def fromEither {t e a : Type u} {ts : List t} {b : Bool} (xs : List t)
  (p : Suffix b xs ts) : Either e a → Result0 ts b
  | Either.left err => Result0.Fail0 err
  | Either.right val => Result0.Succ0 val xs p

--          Conversions

-- NOTE: The following functions use `unsafeCast` because Lean cannot prove
-- that changing the boolean parameter `b` is safe without a more complex
-- definition of `Result0`.

@[inline]
unsafe def swapOr {t e a ts x y} (r : Result0 ts (x || y)) : Result0 ts (y || x) :=
  unsafeCast r

@[inline]
unsafe def orSame {t e a ts x} (r : Result0 ts (x || x)) : Result0 ts x :=
  unsafeCast r

@[inline]
unsafe def orTrue {t e a ts x} (r : Result0 ts (x || true)) : Result0 ts true :=
  unsafeCast r

@[inline]
unsafe def orFalse {t e a ts x} (r : Result0 ts (x || false)) : Result0 ts x :=
  unsafeCast r

@[inline]
unsafe def swapAnd {t e a ts x y} (r : Result0 ts (x && y)) : Result0 ts (y && x) :=
  unsafeCast r

@[inline]
unsafe def andSame {t e a ts x} (r : Result0 ts (x && x)) : Result0 ts x :=
  unsafeCast r

@[inline]
unsafe def andTrue {t e a ts x} (r : Result0 ts (x && true)) : Result0 ts x :=
  unsafeCast r

@[inline]
unsafe def andFalse {t e a ts x} (r : Result0 ts (x && false)) : Result0 ts false :=
  unsafeCast r

@[inline]
unsafe def weaken {t e a ts x} (r : Result0 ts x) : Result0 ts false :=
  unsafeCast r

@[inline]
unsafe def weakens {t e a ts x} (r : Result0 ts true) : Result0 ts x :=
  unsafeCast r

@[inline]
unsafe def and1 {t e a ts x y} (r : Result0 ts x) : Result0 ts (x && y) :=
  unsafeCast r

@[inline]
unsafe def and2 {t e a ts x y} (r : Result0 ts y) : Result0 ts (x && y) :=
  swapAnd (and1 r)

@[inline]
def trans {t e a xs ys b1 b2}
  (res : Result0 xs b1) (p : Suffix b2 xs ys) : Result0 ys (b1 || b2) :=
  match res with
  | Result0.Succ0 val ts q => Result0.Succ0 val ts (trans q p)
  | Result0.Fail0 err => Result0.Fail0 err

--          Combinators

def orElse {t e a ts b1 b2}
  (r1 : Result0 ts b1) (r2 : Thunk (Result0 ts b2)) : Result0 ts (b1 && b2) :=
  match r1 with
  | Result0.Succ0 val xs p => and1 (Result0.Succ0 val xs p)
  | Result0.Fail0 _ => and2 (r2.get)

infix:30 " <|> " => orElse

-- Erased Consumers

inductive TokError (t : Type u) where
  | EOI : TokError t
  | ExpectedEOI : t → TokError t
  | Unexpected : t → TokError t

/-- A tokenizing function that cannot fail. -/
abbrev SafeTok0 (t a : Type u) :=
  {orig : List t} → (xs : List t) → {p : Suffix false xs orig} → Result0 orig true

/--
  A tokenizing function which will consume additional items from the input.
-/
abbrev OntoTok0 (t e a : Type u) :=
  {orig : List t} → (xs : List t) → {p : Suffix false xs orig} → Result0 orig true

def head {t} : OntoTok0 t (TokError t) t :=
  fun xs =>
    match xs with
    | x :: xs' => fun p => Result0.Succ0 x xs' (Suffix.Uncons p)
    | [] => fun p => Result0.Fail0 TokError.EOI

end Data.List.Suffix
