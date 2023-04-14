import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.Order.Lemmas
import Time.ZeroPad

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

instance : Preorder (Fixed p) :=
  @Preorder.lift (Fixed p) Int _ (λ f => f.val)

namespace Fixed

inductive Sign where
  | Nonneg
  | Neg
  deriving Repr, BEq

def toSign (n : Int) : Sign :=
  if n < 0 then Sign.Neg else Sign.Nonneg

theorem toSign_of_neg (n : Int) (h : toSign n == Sign.Neg) : n < 0 := by
  simp [toSign] at h
  aesop_split_hyps
  · simp_all only
  · contradiction

def ico_p_zero (p : Nat) (hp : 0 < p) : Set.Ico 0 p :=
  ⟨0, And.intro (Nat.le_refl 0) hp⟩

private def clip (n : Nat) (p : Nat) (hp : 0 < p) : Set.Ico 0 p :=
  if h : 0 < n then
    if h1 : n ≥ p then
      clip (n / 10) p hp
    else
      ⟨n, And.intro (Nat.le_of_lt h) (Nat.lt_of_not_le h1)⟩
  else
    ico_p_zero p hp
  decreasing_by exact Nat.div_lt_self h (by decide)

private def pow (p : Nat) := 10 ^ p

theorem pow_gt_zero : ∀ {p : ℕ}, 0 < pow p := by
  simp [pow]

theorem pow_gt_zero' : ∀ {p : ℕ}, 0 < (pow p : Int) := by
  simp [pow]

def toFixed (num : Int) (denom : Nat) : Fixed p :=
  let val := Int.natAbs num * (pow p) + (clip denom (pow p) (pow_gt_zero))
  ⟨if num < 0 then Int.negOfNat val else Int.ofNat val⟩

theorem toFixed_eq_toFixed_eval (p : Nat) (n : Int) (denom : Nat) (h : 0 ≤ n)
  : (toFixed n denom : Fixed p) = ⟨n * (pow p) + (clip denom (pow p) (pow_gt_zero))⟩ := by
  simp [toFixed]
  split
  · have h' : n < 0 := by simpa
    exact absurd h' (not_lt_of_le h)
  · simp
    exact Or.inl h

def neg (f : Fixed p) : Fixed p :=
  ⟨-f.val⟩

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
    simp [Int.mul_le_mul_of_nonneg_right (Int.add_one_le_of_lt hnm) (LT.lt.le pow_gt_zero')]

  have h3 : m * pow_p ≤ m * pow_p + ico_m := by
    have : 0 = (ico_p_zero pow_p pow_gt_zero).val := by rw [ico_p_zero]
    have h : m * pow_p = m * pow_p + (ico_p_zero pow_p pow_gt_zero).val := by simpa
    rw [h]
    simp only [le_add_iff_nonneg_right, Nat.cast_nonneg]

  exact Int.lt_of_lt_of_le (Int.lt_of_lt_of_le h1 h2) h3

theorem toFixed_le_toFixed_of_lt (p : Nat) (n : Int) (n_denom : Nat) (m : Int) (m_denom : Nat)
    (hn : 0 ≤ n) (hnm : n < m) :
    (toFixed n n_denom : Fixed p) ≤ (toFixed m m_denom : Fixed p) := by
  have h1 : (toFixed n n_denom : Fixed p).val
      < (toFixed m m_denom : Fixed p).val :=
    toFixed_lt_toFixed p n n_denom m m_denom hn hnm
  have h2 : (toFixed n n_denom : Fixed p).val
      ≤ (toFixed m m_denom : Fixed p).val :=
    LT.lt.le h1
  exact h2

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

def toIco (v : Fixed p) (a b : Fixed p) (h1 : a ≤ v) (h2 : v < b) : Set.Ico a b :=
  ⟨v, And.intro h1 h2⟩

def Int.toFixed (n : Int) (p : Nat) : Fixed p := ⟨n⟩

def divMod' (n : Fixed p) (d : Fixed p) (hd : zero < d) : Int × (Set.Ico zero d) :=
  let n' := n.val / d.val
  let mod := n.val % d.val

  have h0 : 0 < d.val := by simpa

  have h0 : d.val ≠ 0 := by
    apply Ne.symm
    simp [ne_of_lt h0]
  have h1 : 0 < d.val := by simpa

  have h2 : 0 ≤ mod := Int.emod_nonneg n.val h0
  have h3 : mod < d.val := Int.emod_lt_of_pos n.val h1

  have h1' : Fixed.zero ≤ ⟨mod⟩  := by simpa
  have h2' : ⟨mod⟩ < d := by simpa

  (n', toIco ⟨mod⟩ zero d h1' h2')
