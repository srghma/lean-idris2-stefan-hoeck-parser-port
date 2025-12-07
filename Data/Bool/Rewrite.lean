namespace Data.Bool

def replace {a b : α} (p : α → Sort u) (h : a = b) (x : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) x h

@[inline]
def swapOr {x y : Bool} (p : Bool → Type) (v : p (x || y)) : p (y || x) :=
  replace p (Bool.or_comm x y) v

@[inline]
def orSame {x : Bool} (p : Bool → Type) (v : p (x || x)) : p x :=
  replace p (Bool.or_self x) v

@[inline]
def orTrue {x : Bool} (p : Bool → Type) (v : p (x || true)) : p true :=
  replace p (Bool.or_true x) v

@[inline]
def orFalse {x : Bool} (p : Bool → Type) (v : p (x || false)) : p x :=
  replace p (Bool.false_or x) v

@[inline]
def swapAnd {x y : Bool} (p : Bool → Type) (v : p (x && y)) : p (y && x) :=
  replace p (Bool.and_comm x y) v

@[inline]
def andSame {x : Bool} (p : Bool → Type) (v : p (x && x)) : p x :=
  replace p (Bool.and_self x) v

@[inline]
def andTrue {x : Bool} (p : Bool → Type) (v : p (x && true)) : p x :=
  replace p (Bool.true_and x) v

@[inline]
def andFalse {x : Bool} (p : Bool → Type) (v : p (x && false)) : p false :=
  replace p (Bool.false_and x) v

end Data.Bool
