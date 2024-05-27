namespace Time

/-- Reflexive relation of LE class -/
class LeRefl (α : Type u) [LE α] where
  le_refl : ∀ (a : α), a ≤ a

instance : LeRefl Nat where
  le_refl := Nat.le_refl

instance : LeRefl Int where
  le_refl := Int.le_refl

/-- Left-closed right-closed interval -/
def Icc {α : Type} [LE α] (a b : α) := { x : α // a ≤ x ∧ x ≤ b}

instance {α : Type} [LE α] {a b : α} : LE (Icc a b) where
  le a b := LE.le a.val b.val

instance {α : Type} [Repr α] [LE α] {a b : α} : Repr (Icc a b) where
  reprPrec s _ := repr s.val

instance {α : Type} [BEq α] [LE α] {a b : α} : BEq (Icc a b) where
  beq a b := BEq.beq a.val b.val

instance {α : Type} [LE α] {a b : α} : CoeOut (Time.Icc a b) α where
  coe n := n.val

instance {α : Type} [LE α] [LeRefl α]{a b : α}  : LeRefl (Icc a b) where
  le_refl a := LeRefl.le_refl a.val

instance (a b : Nat) : CoeOut (Time.Icc a b) Int where
  coe n := n.val

namespace Icc

theorem nonempty {α : Type} [LE α] [LeRefl α] {a b : α} (h : a ≤ b) : Nonempty (Icc a b) :=
  Nonempty.intro ⟨a, And.intro (LeRefl.le_refl _) h⟩

end Icc

/-- Left-closed right-open interval -/
def Ico {α : Type} [LE α] [LT α] (a b : α) := { x : α // a ≤ x ∧ x < b}

instance {α : Type} [LE α] [LT α] {a b : α} : LE (Ico a b) where
  le a b := LE.le a.val b.val

instance {α : Type} [Repr α] [LE α] [LT α] {a b : α} : Repr (Ico a b) where
  reprPrec s _ := repr s.val

instance {α : Type} [BEq α] [LE α] [LT α] {a b : α} : BEq (Ico a b) where
  beq a b := BEq.beq a.val b.val

instance {α : Type} [LE α] [LT α] (a b : α)  : CoeOut (Time.Ico a b) α where
  coe n := n.val

instance {α : Type} [LE α] [LT α] [LeRefl α]{a b : α}  : LeRefl (Ico a b) where
  le_refl a := LeRefl.le_refl a.val

instance (a b : Nat) : CoeOut (Time.Ico a b) Nat where
  coe n := n.val

instance (a b : Nat) : CoeOut (Time.Ico a b) Int where
  coe n := n.val

namespace Ico

theorem nonempty {α : Type} [LE α] [LT α] [LeRefl α] {a b : α} (h : a < b) : Nonempty (Ico a b) :=
  Nonempty.intro ⟨a, And.intro (LeRefl.le_refl _) h⟩

end Ico

structure NonemptyIcc {α : Type} [LE α] [LeRefl α] (a b : α) where
  icc : Time.Icc a b
  isNonempty : Nonempty (Time.Icc a b)

instance {α : Type} [LE α] [LeRefl α] (a b : α) : Coe (NonemptyIcc a b) (Time.Icc a b) where
  coe n := n.icc

structure NonemptyIco {α : Type} [LE α] [LT α] [LeRefl α] (a b : α) where
  ico : Time.Ico a b
  isNonempty : Nonempty (Time.Ico a b)

instance {α : Type} [LE α] [LT α] [LeRefl α] (a b : α) : Coe (NonemptyIco a b) (Time.Ico a b) where
  coe n := n.ico

def toNonemptyIcc {α : Type} [LE α] [LeRefl α] {a b : α} (v : Time.Icc a b) (h : a <= b)
    : NonemptyIcc a b where
  icc := v
  isNonempty := Icc.nonempty h

def toNonemptyIco {α : Type} [LE α] [LT α] [LeRefl α] {a b : α} (v : Time.Ico a b) (h : a < b)
    : NonemptyIco a b where
  ico := v
  isNonempty := Ico.nonempty h

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
