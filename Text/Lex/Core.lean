import Data.List.Shift
import Data.List.Suffix

universe u

namespace Text.Lex

abbrev Shifter (b : Bool) :=
  SnocList Char → List Char → IO (ShiftRes b)

inductive ShiftRes (b : Bool) where
  | Succ (xs : List Char) (p : Suffix b xs []) : ShiftRes b
  | Stop (start : Suffix false [] []) (errEnd : List Char) (reason : String) : ShiftRes b

inductive Recognise : Bool → Type where
  | Lift (s : Shifter b) : Recognise b
  | Concat (r1 : Recognise b1) (r2 : Recognise b2) : Recognise (b1 || b2)
  | StrictConcat (r1 : Recognise true) (r2 : Recognise b) : Recognise true
  | Alt (r1 : Recognise b1) (r2 : Recognise b2) : Recognise (b1 && b2)

infixl:80 " <+> " => Recognise.Concat
infixl:80 " <++> " => Recognise.StrictConcat
infixl:70 " <|> " => Recognise.Alt

abbrev Lexer := Recognise true

partial def run {b} (r : Recognise b) (st : SnocList Char) (ts : List Char) : IO (ShiftRes b) :=
  match r with
  | Recognise.Lift s => s st ts
  | Recognise.Concat r1 r2 => do
    let res1 ← run r1 st ts
    match res1 with
    | ShiftRes.Succ xs p1 =>
      -- This cast is safe because the only way to construct a `SnocList` is by cons-ing
      -- from an empty list, so the `st` is implicitly carried through.
      let st' := unsafeCast st
      run r2 st' xs
    | ShiftRes.Stop start errEnd reason => pure (ShiftRes.Stop start errEnd reason)
  | Recognise.StrictConcat r1 r2 => do
    let res1 ← run r1 st ts
    match res1 with
    | ShiftRes.Succ xs p1 =>
      let st' := unsafeCast st
      run r2 st' xs
    | ShiftRes.Stop start errEnd reason => pure (ShiftRes.Stop start errEnd reason)
  | Recognise.Alt r1 r2 => do
    let res1 ← run r1 st ts
    match res1 with
    | ShiftRes.Succ .. => pure res1
    | ShiftRes.Stop .. => run r2 st ts

@[inline]
def empty : Recognise false :=
  Recognise.Lift (fun sc cs => pure (ShiftRes.Succ cs Suffix.Same))

@[inline]
def opt (l : Recognise true) : Recognise false :=
  Recognise.Alt l empty

partial def many (r : Recognise true) : Recognise false :=
  opt (Recognise.StrictConcat r (many r))

def some (r : Recognise true) : Recognise true :=
  Recognise.StrictConcat r (many r)

def fail : Recognise true :=
  Recognise.Lift (fun sc cs => pure (ShiftRes.Stop Suffix.Same [] "fail"))

def reject (r : Recognise b) : Recognise false :=
  Recognise.Lift (fun sc cs => do
    let res ← run r sc cs
    match res with
    | ShiftRes.Stop .. => pure (ShiftRes.Succ cs Suffix.Same)
    | ShiftRes.Succ .. => fail sc cs)

def expect (r : Recognise b) : Recognise false :=
  Recognise.Lift (fun sc cs => do
    let res ← run r sc cs
    match res with
    | ShiftRes.Succ .. => pure (ShiftRes.Succ cs Suffix.Same)
    | ShiftRes.Stop start errEnd reason => pure (ShiftRes.Stop start errEnd reason))

end Text.Lex
