import Data.List.Suffix
import Data.Bool.Rewrite

universe u

namespace Data.List.Suffix

/--
  Result of consuming and converting a (possibly strict) prefix of a list of tokens,
  with non-erased proofs for bounds checking.

  - strict: `true` if a strict prefix of the list of tokens has been consumed.
  - t:      The type of token consumed.
  - ts:     The original list of tokens.
  - e:      The error type in case of a failure.
  - a:      The result type.
-/
inductive Result {t e a : Type u} (ts : List t) : Bool → Type u where
  | Succ {b} (val : a) (xs : List t) (p : Suffix b xs ts) : Result ts b
  | Fail {b} {stopStart errEnd : List t}
    (start : Suffix false stopStart ts)
    (p_err : Suffix false errEnd stopStart)
    (reason : e) : Result ts b

/-- Alias for `Succ`, which takes the proof as an explicit argument. -/
@[inline]
def succ' {t e a : Type u} {ts : List t} {b : Bool} (val : a) {xs : List t}
  (p : Suffix b xs ts) : Result ts b :=
  Result.Succ val xs p

instance {t e : Type u} {ts : List t} {b : Bool} : Functor (Result ts b) where
  map f
    | Result.Succ v xs p => Result.Succ (f v) xs p
    | Result.Fail start p_err reason => Result.Fail start p_err reason

--          Conversions

-- NOTE: The following functions use `unsafeCast` because Lean cannot prove
-- that changing the boolean parameter `b` is safe without a more complex
-
@[inline]
unsafe def swapOr {t e a ts x y} (r : Result ts (x || y)) : Result ts (y || x) :=
  unsafeCast r

@[inline]
unsafe def orSame {t e a ts x} (r : Result ts (x || x)) : Result ts x :=
  unsafeCast r

@[inline]
unsafe def orTrue {t e a ts x} (r : Result ts (x || true)) : Result ts true :=
  unsafeCast r

@[inline]
unsafe def orFalse {t e a ts x} (r : Result ts (x || false)) : Result ts x :=
  unsafeCast r

@[inline]
unsafe def swapAnd {t e a ts x y} (r : Result ts (x && y)) : Result ts (y && x) :=
  unsafeCast r

@[inline]
unsafe def andSame {t e a ts x} (r : Result ts (x && x)) : Result ts x :=
  unsafeCast r

@[inline]
unsafe def andTrue {t e a ts x} (r : Result ts (x && true)) : Result ts x :=
  unsafeCast r

@[inline]
unsafe def andFalse {t e a ts x} (r : Result ts (x && false)) : Result ts false :=
  unsafeCast r

@[inline]
unsafe def weaken {t e a ts x} (r : Result ts x) : Result ts false :=
  unsafeCast r

@[inline]
unsafe def weakens {t e a ts x} (r : Result ts true) : Result ts x :=
  unsafeCast r

@[inline]
unsafe def and1 {t e a ts x y} (r : Result ts x) : Result ts (x && y) :=
  unsafeCast r

@[inline]
unsafe def and2 {t e a ts x y} (r : Result ts y) : Result ts (x && y) :=
  swapAnd (and1 r)

@[inline]
unsafe def trans {t e a xs ys b1 b2}
  (res : Result xs b1) (p : Suffix b2 xs ys) : Result ys (b1 || b2) :=
  match res with
  | Result.Succ val ts q => Result.Succ val ts (Suffix.trans q p)
  | Result.Fail start p_err reason =>
    Result.Fail (Suffix.weaken (Suffix.trans start p)) p_err reason

end Data.List.Suffix
