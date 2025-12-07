import Data.List.Suffix
import Text.Lex.Tokenizer

universe u

namespace Text.Parse

open Text.Lex

inductive Res (b : Bool) (t : Type u) (ts : List (Bounded t)) (state e a : Type u) where
  | Fail (consumed : Bool) (err : List (Bounded (InnerError e))) : Res b t ts state e a
  | Succ (st : state) (res : Bounded a) (toks : List (Bounded t)) (prf : Suffix b toks ts) : Res b t ts state e a

inductive Grammar : Bool → Type u → Type u → Type u → Type u → Type u → Type u where
  | Lift {b state t e a} : (state → (ts : List (Bounded t)) → Res b t ts state e a) → Grammar b state t e a
  | App {b1 b2 state t e a b} : Grammar b1 state t e (a → b) → Grammar b2 state t e a → Grammar (b1 || b2) state t e b
  | AppEat {b2 state t e a b} : Grammar true state t e (a → b) → Grammar b2 state t e a → Grammar true state t e b
  | Bind {b1 b2 state t e a b} : Grammar b1 state t e a → (a → Grammar b2 state t e b) → Grammar (b1 || b2) state t e b
  | BindEat {b2 state t e a b} : Grammar true state t e a → (a → Grammar b2 state t e b) → Grammar true state t e b
  | Alt {b1 b2 state t e a} : Grammar b1 state t e a → Thunk (Grammar b2 state t e a) → Grammar (b1 && b2) state t e a
  | Bounds {b state t e a} : Grammar b state t e a → Grammar b state t e (Bounded a)
  | Try {b state t e a} : Grammar b state t e a → Grammar b state t e a

infixl:70 " <|> " => Grammar.Alt

partial def prs {b state t e a} (g : Grammar b state t e a) (st : state) (consumed : Bool)
  (ts : List (Bounded t)) : Res b t ts state e a :=
  match g with
  | Grammar.Lift f => f st ts
  | Grammar.App g1 g2 =>
    match prs g1 st consumed ts with
    | Res.Succ st' f toks prf =>
      match prs g2 st' (consumed || prf.len > 0) toks with
      | Res.Succ st'' v toks' prf' =>
        let bds := { start := f.bounds.start, fin := v.bounds.fin }
        Res.Succ st'' { val := f.val v.val, bounds := bds } toks' (prf'.trans prf)
      | Res.Fail c err => Res.Fail (consumed || c) err
    | Res.Fail c err => Res.Fail c err
  | Grammar.AppEat g1 g2 =>
    match prs g1 st consumed ts with
    | Res.Succ st' f toks prf =>
      match prs g2 st' true toks with
      | Res.Succ st'' v toks' prf' =>
        let bds := { start := f.bounds.start, fin := v.bounds.fin }
        Res.Succ st'' { val := f.val v.val, bounds := bds } toks' (prf'.trans prf)
      | Res.Fail c err => Res.Fail (consumed || c) err
    | Res.Fail c err => Res.Fail c err
  | Grammar.Bind g1 g2 =>
    match prs g1 st consumed ts with
    | Res.Succ st' v toks prf =>
      prs (g2 v.val) st' (consumed || prf.len > 0) toks
    | Res.Fail c err => Res.Fail c err
  | Grammar.BindEat g1 g2 =>
    match prs g1 st consumed ts with
    | Res.Succ st' v toks prf =>
      prs (g2 v.val) st' true toks
    | Res.Fail c err => Res.Fail c err
  | Grammar.Alt g1 g2 =>
    match prs g1 st false ts with
    | res@(Res.Succ ..) => res
    | Res.Fail c1 err1 =>
      if c1 then Res.Fail c1 err1
      else
        match prs (g2.get) st false ts with
        | res@(Res.Succ ..) => res
        | Res.Fail c2 err2 => Res.Fail (c1 || c2) (err1 ++ err2)
  | Grammar.Bounds g' =>
    match prs g' st consumed ts with
    | Res.Succ st' v toks prf =>
      Res.Succ st' { val := v, bounds := v.bounds } toks prf
    | Res.Fail c err => Res.Fail c err
  | Grammar.Try g' =>
    match prs g' st consumed ts with
    | Res.Fail _ err => Res.Fail false err
    | res => res

def parse {b state t e a} (g : Grammar b state t e a) (st : state) (ts : List (Bounded t)) :
  Except (List (Bounded (InnerError e))) (state × a × List (Bounded t)) :=
  match prs g st false ts with
  | Res.Fail _ errs => Except.error errs
  | Res.Succ st' res toks _ => Except.ok (st', res.val, toks)

end Text.Parse
