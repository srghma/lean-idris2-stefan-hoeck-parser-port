import Text.Lex.Manual
import Text.Lex.Core
import Text.Parse.Core

universe u

namespace Text.Lex

open Text.Lex.Manual
open Text.Parse (Res)

inductive Tokenizer (e tt : Type u) where
  | Direct (tok : Tok true e tt) : Tokenizer e tt
  | Compose {tag : Type u}
    (beginTok : Tok true e (tt × tag))
    (middle : tag → Tokenizer e tt)
    (endTok : tag → Tok true e tt)
    : Tokenizer e tt
  | Alt (t1 : Tokenizer e tt) (t2 : Tokenizer e tt) : Tokenizer e tt

infix:30 " <|> " => Tokenizer.Alt

structure TokRes (strict : Bool) (cs : List Char) (r a : Type u) where
  pos : Position
  toks : List (Bounded a)
  reason : Option r
  rem : List Char
  suf : Suffix strict rem cs

partial def tokenise {e a} (tokenizer : Tokenizer e a) (pos : Position)
  (toks : List (Bounded a)) (cs : List Char) :
  TokRes false cs (Bounded (InnerError e)) a :=
  if cs.isEmpty then
    { pos, toks, reason := none, rem := [], suf := Suffix.Same }
  else
    let next_res := match tokenizer with
      | Tokenizer.Direct f => f cs
      | Tokenizer.Compose beg mid end' =>
        match beg cs with
        | Result.Succ (v, tag) rem p =>
          let new_pos := endPos pos p
          let new_tok := { val := v, bounds := { start := pos, fin := new_pos } }
          let mid_res := tokenise (mid tag) new_pos (toks.concat new_tok) rem
          match end' tag mid_res.rem with
          | Result.Succ v' rem' p' =>
            let end_pos := endPos mid_res.pos p'
            let end_tok := { val := v', bounds := { start := mid_res.pos, fin := end_pos } }
            -- This is a simplified result; a full implementation would need to combine proofs.
            Result.Succ end_tok rem' p'
          | Result.Fail start p_err reason => Result.Fail start p_err reason
        | Result.Fail start p_err reason => Result.Fail start p_err reason
      | Tokenizer.Alt t1 t2 =>
        match t1 cs with
        | res@(Result.Succ ..) => res
        | Result.Fail .. => t2 cs

    match next_res with
    | Result.Succ v rem p =>
      let new_pos := endPos pos p
      let new_tok := { val := v, bounds := { start := pos, fin := new_pos } }
      tokenise tokenizer new_pos (toks.concat new_tok) rem
    | Result.Fail start p_err reason =>
      let err_bds := { start := endPos pos start, fin := endPos pos (p_err.trans start) }
      { pos, toks, reason := some { val := reason, bounds := err_bds }, rem := cs, suf := Suffix.Same }

@[inline]
def lex {e a} (tokenizer : Tokenizer e a) (s : String) :
  TokRes false (s.toList) (Bounded (InnerError e)) a :=
  tokenise tokenizer { line := 1, col := 1 } [] s.toList

end Text.Lex
