import Time.Interval

namespace Time

def zeroLPad (s : String) (n : Nat) : String :=
  (String.pushn "" '0' (n - s.length)) ++ s

def zeroRPad (s : String) (n : Nat) : String :=
  s ++ (String.pushn "" '0' (n - s.length))

class ToZeroPadded (α : Type u) where
  toZeroPadded : α → Nat → String

export ToZeroPadded (toZeroPadded)

instance : ToZeroPadded Int where
  toZeroPadded n i := zeroLPad (toString (if n < 0 then Neg.neg n else n)) i

instance  {a b : Nat} : ToZeroPadded (Time.Icc a b) where
  toZeroPadded n i := zeroLPad (toString n.val) i

/-
instance  {a b : α} [ToString α] : ToZeroPadded (Time.Ico a b) where
  toZeroPadded n i := zeroLPad (toString n.val) i
-/

instance : ToZeroPadded Nat where
  toZeroPadded n i := zeroLPad (toString n) i
