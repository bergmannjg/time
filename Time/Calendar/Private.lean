import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Fin.Basic
import Time.Fixed

namespace Time

namespace Private

structure NonemptyIcc (a b : Nat) where
  icc : Set.Icc a b
  isNonempty : (Set.Icc a b).Nonempty

instance : Coe (NonemptyIcc a b) (Set.Icc a b) where
  coe n := n.icc

structure NonemptyIco (a b : Nat) where
  ico : Set.Ico a b
  isNonempty : (Set.Ico a b).Nonempty

instance : Coe (NonemptyIco a b) (Set.Ico a b) where
  coe n := n.ico

def toNonemptyIcc (v : Set.Icc a b) (h : a <= b) : NonemptyIcc a b where
  icc := v
  isNonempty := Set.nonempty_Icc.mpr h

def toNonemptyIco (v : Set.Ico a b) (h : a < b) : NonemptyIco a b where
  ico := v
  isNonempty := Set.nonempty_Ico.mpr h

namespace NonemptyIcc

theorem sub_lt_sub : ∀ {n x m : Nat}, n <= x → x < m → n < m → x - n < m - n
  | 0, _, _, _, h2, _ => by
    exact h2
  | n+1,x+1,m+1,h1,h2,h3 => by
    rewrite [Nat.add_sub_add_right, Nat.add_sub_add_right]
    exact sub_lt_sub
      (Nat.le_of_succ_le_succ h1) (Nat.lt_of_succ_lt_succ h2) (Nat.lt_of_succ_lt_succ h3)

theorem sub_lt_sub_of_succ : ∀ {n x m : Nat}, n <= x → x <= m → n <= m → x - n < m + 1 - n
  | n,x,m,h1,h2,h3 => by
    have h2' : x < m + 1 := by exact (Nat.lt_succ_of_le h2)
    have h3' : n < m + 1 := by exact (Nat.lt_succ_of_le h3)
    exact sub_lt_sub h1 h2' h3'

def toFin (x : NonemptyIcc n m) : Fin (m + 1 - n) :=
  have h1 : n <= x.icc.val := x.icc.property.left
  have h2 : x.icc.val <= m := x.icc.property.right
  have h : n <= m := Nat.le_trans h1 h2
  Fin.mk (x.icc.val - n) (by simp [sub_lt_sub_of_succ h1 h2 h])

instance : Coe (NonemptyIcc n m) (Fin (m + 1 - n)) where
  coe x := toFin x

instance : Coe (NonemptyIcc 1 m) (Fin m) where
  coe x := Fin.cast (by simp) <| toFin x

end NonemptyIcc

def clip' (a : Nat) (b : Nat) (x : Int) (h : a <= b) : NonemptyIcc a b :=
  let x'' := x.toNat
  let icc : Set.Icc a b :=
    if ha : x'' < a then ⟨a, And.intro (by simp) h⟩
    else if hb : x'' > b then ⟨b, And.intro h (by simp)⟩
    else
      ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_lt.1 hb) ⟩

  toNonemptyIcc icc h

def clip (a : Nat) (b : Nat) (x : Int) (h : a <= b) : Nat :=
  (clip' a b x h).icc.val

def clipValid' (a : Nat) (b : Nat) (x : Int) (h : a <= b) : Option $ NonemptyIcc a b :=
  let x'' := x.toNat
  let icc : Option $ Set.Icc a b :=
    if ha : x'' < a then none
    else if hb : x'' > b then none
    else
      some ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_lt.1 hb) ⟩

  icc |> Option.map (λ icc => toNonemptyIcc icc h)

def clipValid'' (a : Nat) (b : Nat) (x : Int) (h : a < b) : Option $ NonemptyIco a b :=
  let x'' := x.toNat
  let ico : Option $ Set.Ico a b :=
    if ha : x'' < a then none
    else if hb : x'' >= b then none
    else
      some ⟨x'', And.intro (Nat.not_lt.1 ha) (Nat.not_le.1 hb) ⟩

  ico |> Option.map (λ ico => toNonemptyIco ico h)

def clipValid (a : Nat) (b : Nat) (x : Int) (h : a <= b) : Option Nat :=
  clipValid' a b x h |> Option.map (λ v => v.icc)

def clipValid''' (a : Fixed p) (b : Fixed p) (x : Fixed p) : Option $ Set.Ico a b :=
  let ico : Option $ Set.Ico a b :=
    if ha : a ≤ x then
      if hb : x < b then
        some ⟨x, And.intro ha hb⟩
      else none
    else none

  ico
