import Data.List.Suffix.Result

universe u

namespace Text.Lex.Manual

-- Placeholders for Tok and AutoTok, which are defined in `Text.Lex.Manual`.
-- These definitions are simplified to allow the syntax to be translated.
abbrev Tok (b : Bool) (e a : Type u) :=
  (cs : List Char) → Result cs b (α := a) (ε := e)

abbrev AutoTok (e a : Type u) :=
  (cs : List Char) → Result cs true (α := a) (ε := e)

namespace Tok

  def pure {e a : Type u} (v : a) : Tok false e a :=
    fun cs => Result.Succ v cs Suffix.Same

  def bind {e a b : Type u} {b1 b2 : Bool}
    (f : Tok b1 e a) (g : a → Tok b2 e b) : Tok (b1 || b2) e b :=
    fun cs =>
      match f cs with
      | Result.Succ x cs1 p =>
        let res := g x cs1
        Result.trans res p
      | Result.Fail start p_err reason => Result.Fail start p_err reason

  def seq {e a : Type u} {b1 b2 : Bool}
    (f : Tok b1 e Unit) (g : Tok b2 e a) : Tok (b1 || b2) e a :=
    bind f (fun _ => g)

  def map {e a b : Type u} {b1 b2 : Bool}
    (f : a → b) (t : Tok b1 e a) : Tok b1 e b :=
    fun cs =>
      match t cs with
      | Result.Succ v cs' p => Result.Succ (f v) cs' p
      | Result.Fail start p_err reason => Result.Fail start p_err reason

  instance {e : Type u} {b : Bool} : Monad (Tok b e) where
    pure := pure
    bind := fun x y => bind x y

end Tok

namespace AutoTok

  def pure {e a : Type u} (v : a) : AutoTok e a :=
    fun cs => Result.Succ v cs Suffix.Same

  def bind {e a b : Type u}
    (f : AutoTok e a) (g : a → AutoTok e b) : AutoTok e b :=
    fun cs =>
      match f cs with
      | Result.Succ x cs1 p => g x cs1
      | Result.Fail start p_err reason => Result.Fail start p_err reason

  def seq {e a : Type u}
    (f : AutoTok e Unit) (g : AutoTok e a) : AutoTok e a :=
    bind f (fun _ => g)

  def map {e a b : Type u}
    (f : a → b) (t : AutoTok e a) : AutoTok e b :=
    fun cs =>
      match t cs with
      | Result.Succ v cs' p => Result.Succ (f v) cs' p
      | Result.Fail start p_err reason => Result.Fail start p_err reason

  instance {e : Type u} : Monad (AutoTok e) where
    pure := pure
    bind := bind

end AutoTok

end Text.Lex.Manual
