import Data.Bool.Rewrite
import Data.List.Suffix

universe u

namespace Data.List

abbrev SnocList (α : Type u) : Type u := List α
def snoc {α : Type u} (xs : SnocList α) (x : α) : SnocList α := x :: xs

/--
  Witness that a pair of a snoclist and a list is the result of shifting
  values from the head of an initial list to the tail of an initial snoclist.
  Represented by the number of shifted elements.
-/
structure Shift {t : Type u} (b : Bool) (sx : SnocList t) (xs : List t) (giro : SnocList t) (orig : List t) where
  len : Nat

def Shift.Same {t sx xs} : Shift (t:=t) false sx xs sx xs := { len := 0 }

def Shift.SH {t b sx sy x xs ys} (s : Shift (t:=t) b sx (x :: xs) sy ys) : Shift true (snoc sx x) xs sy ys :=
  { len := s.len + 1 }

@[inline]
def Shift.toNat {t b sx xs sy ys} (s : Shift (t:=t) b sx xs sy ys) : Nat := s.len

--          Conversions

@[inline]
def Shift.weaken {t b sx xs sy ys} (s : Shift (t:=t) b sx xs sy ys) : Shift false sx xs sy ys :=
  { len := s.len }

@[inline]
def Shift.weakens {t b sx xs sy ys} (s : Shift (t:=t) true sx xs sy ys) : Shift b sx xs sy ys :=
  { len := s.len }

@[inline]
def Shift.trans {t b1 b2 sx xs sy ys sz zs}
  (s1 : Shift (t:=t) b1 sx xs sy ys) (s2 : Shift b2 sy ys sz zs) : Shift (b1 || b2) sx xs sz zs :=
  { len := s1.len + s2.len }

def Shift.toSuffix {t b sx xs sy ys} (s : Shift (t:=t) b sx xs sy ys) : Suffix b xs ys :=
  { len := s.len }

end Data.List
