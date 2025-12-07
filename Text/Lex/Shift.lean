import Data.List.Shift
import Text.Lex.Manual

universe u

namespace Text.Lex

open Text.Lex.Manual

@[inline]
def shift (p : Position) {b t} {sx xs sy ys} (s : Data.List.Shift (t:=t) b sx xs sy ys) : Position :=
  { p with col := p.col + s.toNat }

inductive ShiftRes (b : Bool) (sc : SnocList Char) (cs : List Char) : Type where
  | Succ {pre : SnocList Char} (post : List Char)
    (sh : Data.List.Shift (t:=Char) b pre post sc cs) : ShiftRes b sc cs
  | Stop {se ee : SnocList Char} {errStart : List Char}
    (start : Data.List.Shift (t:=Char) false se errStart sc cs)
    (errEnd : List Char)
    (end_proof : Data.List.Shift (t:=Char) false ee errEnd se errStart)
    (reason : InnerError Unit)
    : ShiftRes b sc cs

def suffix {e a} (f : SnocList Char → a) {cs} (res : ShiftRes true [] cs) : LexRes true cs e a :=
  sorry -- Depends on Data.List.Shift.suffix, which is not fully translated.

-- Conversions
@[inline] unsafe def swapOr {b sc cs x y} (r : ShiftRes (x || y) sc cs) : ShiftRes (y || x) sc cs := unsafeCast r
@[inline] unsafe def orSame {b sc cs x} (r : ShiftRes (x || x) sc cs) : ShiftRes x sc cs := unsafeCast r
@[inline] unsafe def orTrue {b sc cs x} (r : ShiftRes (x || true) sc cs) : ShiftRes true sc cs := unsafeCast r
@[inline] unsafe def orFalse {b sc cs x} (r : ShiftRes (x || false) sc cs) : ShiftRes x sc cs := unsafeCast r
@[inline] unsafe def swapAnd {b sc cs x y} (r : ShiftRes (x && y) sc cs) : ShiftRes (y && x) sc cs := unsafeCast r
@[inline] unsafe def andSame {b sc cs x} (r : ShiftRes (x && x) sc cs) : ShiftRes x sc cs := unsafeCast r
@[inline] unsafe def andTrue {b sc cs x} (r : ShiftRes (x && true) sc cs) : ShiftRes x sc cs := unsafeCast r
@[inline] unsafe def andFalse {b sc cs x} (r : ShiftRes (x && false) sc cs) : ShiftRes false sc cs := unsafeCast r
@[inline] unsafe def weaken {b sc cs x} (r : ShiftRes x sc cs) : ShiftRes false sc cs := unsafeCast r
@[inline] unsafe def weakens {b sc cs x} (r : ShiftRes true sc cs) : ShiftRes x sc cs := unsafeCast r
@[inline] unsafe def and1 {b sc cs x y} (r : ShiftRes x sc cs) : ShiftRes (x && y) sc cs := unsafeCast r
@[inline] unsafe def and2 {b sc cs x y} (r : ShiftRes x sc cs) : ShiftRes (y && x) sc cs := swapAnd (and1 r)

-- Combinators
def orElse {b1 b2 sx xs} (r1 : ShiftRes b1 sx xs) (r2 : Thunk (ShiftRes b2 sx xs)) : ShiftRes (b1 && b2) sx xs :=
  match r1 with
  | ShiftRes.Succ post sh => and1 (ShiftRes.Succ post sh)
  | ShiftRes.Stop .. => and2 r2.get

infix:30 " <|> " => orElse

-- Shifters
abbrev Shifter (b : Bool) :=
  (st : SnocList Char) → (ts : List Char) → ShiftRes b st ts

abbrev AutoShift (s : Bool) :=
  {b : Bool} → {giro : SnocList Char} → {orig : List Char} →
  {pre : SnocList Char} → (post : List Char) →
  (sh : Data.List.Shift b pre post giro orig) → ShiftRes (s || b) giro orig

def eoiAt {b1 b2 giro ruc orig} (sh : Data.List.Shift b1 ruc [] giro orig) : ShiftRes b2 giro orig :=
  ShiftRes.Stop (Data.List.Shift.weaken sh) [] sh (InnerError.EOI)

def unknown {b bres giro ruc c orig errEnd}
  (sh : Data.List.Shift b ruc (c :: errEnd) giro orig) : ShiftRes bres giro orig :=
  let sh' := Data.List.Shift.weaken sh
  ShiftRes.Stop sh' (c :: errEnd) Data.List.Shift.Same (InnerError.Unknown (String.singleton c))

def one (f : Char → Bool) : AutoShift true :=
  fun post sh =>
    match post with
    | x :: xs => if f x then ShiftRes.Succ xs (Data.List.Shift.SH sh) else unknown sh
    | [] => eoiAt sh

def takeWhile (f : Char → Bool) : AutoShift false :=
  fun post sh =>
    match post with
    | x :: xs => if f x then takeWhile f xs (Data.List.Shift.SH sh) else ShiftRes.Succ (x::xs) sh
    | [] => ShiftRes.Succ [] sh

def takeWhile1 (f : Char → Bool) : AutoShift true :=
  fun post sh =>
    match post with
    | x :: xs => if f x then takeWhile f xs (Data.List.Shift.SH sh) else unknown sh
    | [] => eoiAt sh

def string : Shifter true :=
  let rec str {b giro orig pre} (post) (sh : Data.List.Shift b pre post giro orig) : ShiftRes (true || b) giro orig :=
    match post with
    | '"' :: xs => ShiftRes.Succ xs (Data.List.Shift.SH sh)
    | '\\' :: x :: xs => str xs (Data.List.Shift.SH (Data.List.Shift.SH sh))
    | x :: xs => str xs (Data.List.Shift.SH sh)
    | [] => eoiAt sh
  fun sc cs =>
    match cs with
    | '"' :: xs => str xs (Data.List.Shift.SH Data.List.Shift.Same)
    | h :: t => unknown Data.List.Shift.Same
    | [] => eoiAt Data.List.Shift.Same

end Text.Lex
