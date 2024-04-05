import Std.Data.Int.Order
import Time.ZeroPad
import Time.Interval

namespace Time

/--  fixed-point representation of a fractional number -/
structure Fixed (precision : Nat) where
  val : Int
  deriving Repr, BEq, DecidableEq

def Fixed.zero : (Fixed p) := ⟨0⟩

instance : Inhabited (Fixed p) where
  default := Fixed.zero

instance {p} : LT (Fixed p) where
  lt a b := LT.lt a.val b.val

instance {p} : LE (Fixed p) where
  le a b := LE.le a.val b.val

instance {p} : LeRefl (Fixed p) where
  le_refl a := LeRefl.le_refl a.val

namespace Fixed

inductive Sign where
  | Nonneg
  | Neg
  deriving Repr, BEq

def toSign (n : Int) : Sign :=
  if n < 0 then Sign.Neg else Sign.Nonneg

def ico_p_zero (p : Nat) (hp : 0 < p) : Time.Ico 0 p :=
  ⟨0, And.intro (Nat.le_refl 0) hp⟩

private def clip (n : Nat) (p : Nat) (hp : 0 < p) : Time.Ico 0 p :=
  if h : 0 < n then
    if h1 : n ≥ p then
      clip (n / 10) p hp
    else
      ⟨n, And.intro (Nat.le_of_lt h) (Nat.lt_of_not_le h1)⟩
  else
    ico_p_zero p hp
  decreasing_by exact Nat.div_lt_self h (by decide)

private def pow (p : Nat) := Nat.pow 10 p

private theorem pow_gt_zero : ∀ {p : Nat}, 0 < pow p := by
  unfold Fixed.pow Nat.pow
  intro p
  induction p
  case zero => split <;> simp_all
  case succ n ih =>
    split at ih <;> simp_all
    omega

private theorem pow_gt_zero' : ∀ {p : Nat}, 0 < (pow p : Int) := by
  simp [Int.ofNat]
  simp [pow_gt_zero]

def toFixed (num : Int) (denom : Nat) : Fixed p :=
  let val := Int.natAbs num * (pow p) + (clip denom (pow p) (pow_gt_zero)).val
  ⟨if num < 0 then Int.negOfNat val else Int.ofNat val⟩

private theorem toFixed_eq_toFixed_eval (p : Nat) (n : Int) (denom : Nat) (h : 0 ≤ n)
  : (toFixed n denom : Fixed p) = ⟨n * (pow p) + (clip denom (pow p) (pow_gt_zero)).val⟩ := by
  simp [toFixed]
  split
  · have h' : n < 0 := by simpa
    exact absurd h' (Int.not_lt.2 h)
  · simp
    have : (Int.natAbs n) = n := by omega
    simp_all

def neg (f : Fixed p) : Fixed p :=
  ⟨-f.val⟩

private theorem toFixed_eq_zero (p : Nat) : (toFixed 0 0 : Fixed p) = Fixed.zero := by
  unfold Fixed.toFixed Fixed.zero
  split <;> simp_all
  unfold Fixed.clip ico_p_zero
  simp

theorem toFixed_lt_toFixed (p : Nat) (n : Int) (n_denom : Nat) (m : Int) (m_denom : Nat)
    (hn : 0 ≤ n) (hnm : n < m) :
    (toFixed n n_denom : Fixed p) < (toFixed m m_denom : Fixed p) := by
  have hm : 0 ≤ m := Int.le_of_lt <| Int.lt_of_le_of_lt hn hnm
  rw [toFixed_eq_toFixed_eval _ _ _ hn, toFixed_eq_toFixed_eval  _ _ _ hm]

  let pow_p := pow p
  let ico_n := clip n_denom pow_p pow_gt_zero
  let ico_m := clip m_denom pow_p pow_gt_zero

  have h1 : n * pow_p + ico_n < (n + 1) * pow_p := by
    have h1 : ico_n.val < pow_p := ico_n.property.right
    have h2 : n * pow_p + pow_p = (n + 1) * pow_p := by
      simp [Int.add_mul]
    have h3 : n * pow_p + ico_n.val < n * pow_p + pow_p :=
      Int.add_lt_add_of_le_of_lt (Int.le_refl (n * pow_p)) (Int.ofNat_lt.mpr h1)
    rw [← h2]
    exact h3

  have h2 : (n + 1) * pow_p ≤ m * pow_p := by
    simp [Int.mul_le_mul_of_nonneg_right (Int.add_one_le_of_lt hnm) (Int.le_of_lt pow_gt_zero')]

  have h3 : m * pow_p ≤ m * pow_p + ico_m.val := by omega

  exact Int.lt_of_lt_of_le (Int.lt_of_lt_of_le h1 h2) h3

theorem zero_lt_toFixed (p : Nat) (m : Int) (m_denom : Nat) (hnm : 0 < m)
    : Fixed.zero < (toFixed m m_denom : Fixed p) := by
  have : toFixed 0 0 < (toFixed m m_denom : Fixed p) :=
    toFixed_lt_toFixed p _ _ m m_denom (by omega) hnm
  rw [← toFixed_eq_zero p]
  simp [this]

theorem toFixed_le_toFixed_of_lt (p : Nat) (n : Int) (n_denom : Nat) (m : Int) (m_denom : Nat)
    (hn : 0 ≤ n) (hnm : n < m) :
    (toFixed n n_denom : Fixed p) ≤ (toFixed m m_denom : Fixed p) := by
  have h1 : (toFixed n n_denom : Fixed p).val
      < (toFixed m m_denom : Fixed p).val :=
    toFixed_lt_toFixed p n n_denom m m_denom hn hnm
  have h2 : (toFixed n n_denom : Fixed p).val
      ≤ (toFixed m m_denom : Fixed p).val := by
    simp [Int.le_of_lt h1]
  exact h2

theorem zero_le_toFixed (p : Nat) (m : Int) (m_denom : Nat) (hnm : 0 < m)
    : Fixed.zero ≤ (toFixed m m_denom : Fixed p) := by
  have : toFixed 0 0 < (toFixed m m_denom : Fixed p) :=
    toFixed_lt_toFixed p _ _ m m_denom (by omega) hnm
  have : toFixed 0 0 ≤ (toFixed m m_denom : Fixed p) := by
    have h : (toFixed 0 0 : Fixed p).val
        ≤ (toFixed m m_denom : Fixed p).val := by
      simp [Int.le_of_lt this]
    exact h
  rw [← toFixed_eq_zero p]
  simp [this]

private def divMod'' (n : Int) (p : Nat) : Int × Nat :=
  let (n', d') := (n / p, n % p)
  ⟨n', d'.toNat⟩

def numeratorDenominator (f : Fixed p) : Sign × Int × Nat :=
  ⟨if f.val < 0 then .Neg else .Nonneg, divMod'' f.val.natAbs (pow p)⟩

def numerator (f : Fixed p) : Int :=
  let (_, n, _) := numeratorDenominator f
  n

def denominatorValueToString (d : Int) (p : Nat) : String :=
    let dropped := (toZeroPadded d p).toSubstring.dropRightWhile (λ c => c == '0')
    let s := dropped.toString
    if s != "" then "." ++ s else s

def denominatorToString (f : Fixed p) : String :=
    let (_, _, d) := numeratorDenominator f
    denominatorValueToString d p

instance : ToString (Fixed p) where
  toString a :=
    let (s, n, d) := numeratorDenominator a
    let sign := if s == .Neg then "-" else ""
    if d != 0 then s!"{sign}{n}{denominatorValueToString d p}" else s!"{n}"

def sub (dt1 dt2 : Fixed p) : Fixed p :=
  ⟨dt1.val - dt2.val⟩

def add (dt1 dt2 : Fixed p) : Fixed p :=
  ⟨dt1.val + dt2.val⟩

def divMod (n : Fixed p) (d : Fixed p) : Int × Fixed p :=
  (n.val / d.val, ⟨n.val % d.val⟩)

instance : Sub (Fixed p) where
  sub := sub

instance : Add (Fixed p) where
  add := add

def toIco (v : Fixed p) (a b : Fixed p) (h1 : a ≤ v) (h2 : v < b) : Time.Ico a b :=
  ⟨v, And.intro h1 h2⟩

def Int.toFixed (n : Int) (p : Nat) : Fixed p := ⟨n⟩

def divMod' (n : Fixed p) (d : Fixed p) (hd : zero < d) : Int × (Time.Ico zero d) :=
  let n' := n.val / d.val
  let mod := n.val % d.val

  have : 0 < d.val := by simpa
  have h0 : d.val ≠ 0 := by omega
  have h1 : 0 < d.val := by omega

  have h2 : 0 ≤ mod := Int.emod_nonneg n.val h0
  have h3 : mod < d.val := Int.emod_lt_of_pos n.val h1

  have h1' : Fixed.zero ≤ ⟨mod⟩  := by simpa
  have h2' : ⟨mod⟩ < d := by simpa

  (n', toIco ⟨mod⟩ zero d h1' h2')
