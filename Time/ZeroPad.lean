import Mathlib.Data.Set.Intervals.Basic

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

instance  {a : Int} : ToZeroPadded (Set.Ici a) where
  toZeroPadded n i := zeroLPad (toString (if n.val < 0 then Neg.neg n.val else n.val)) i

instance  {a : Nat} : ToZeroPadded (Set.Ici a) where
  toZeroPadded n i := zeroLPad (toString n.val) i

instance  {a b : Nat} : ToZeroPadded (Set.Icc a b) where
  toZeroPadded n i := zeroLPad (toString n.val) i

instance  {a b : α} [Preorder α] [ToString α] : ToZeroPadded (Set.Ico a b) where
  toZeroPadded n i := zeroLPad (toString n.val) i

instance : ToZeroPadded Nat where
  toZeroPadded n i := zeroLPad (toString n) i
