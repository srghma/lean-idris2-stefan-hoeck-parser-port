import Data.Bool.Rewrite

universe u

namespace Data.List

/--
  Proof that a list is a (possibly strict) suffix of another list.
  This is represented by the number of elements dropped from the original list.
-/
structure Suffix (b : Bool) (xs ys : List α) where
  len : Nat

def Suffix.Same {xs : List α} : Suffix false xs xs := { len := 0 }

def Suffix.Uncons {b x xs ys} (p : Suffix b xs ys) : Suffix true xs (x :: ys) :=
  { len := p.len + 1 }

@[inline]
def Suffix.toNat {b xs ys} (s : Suffix b xs ys) : Nat := s.len

--          Conversions
-- These are now simple manipulations of the boolean flag and length.

@[inline]
def Suffix.weaken {b xs ys} (s : Suffix b xs ys) : Suffix false xs ys :=
  { len := s.len }

@[inline]
def Suffix.weakens {b xs ys} (s : Suffix true xs ys) : Suffix b xs ys :=
  { len := s.len }

@[inline]
def Suffix.trans {b1 b2 xs ys zs} (s1 : Suffix b1 xs ys) (s2 : Suffix b2 ys zs) : Suffix (b1 || b2) xs zs :=
  { len := s1.len + s2.len }

end Data.List
