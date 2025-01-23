import Init.Data.Int.Order
import Init.Data.Int.DivMod
import Time.ZeroPad
import Time.Data.Int.Order

namespace Time

/--  fixed-point representation of a fractional number -/
@[ext] structure Fixed (precision : Nat) where
  val : Int
  deriving Repr, BEq, DecidableEq

inductive Sign where
  | Nonneg
  | Neg
  deriving Repr, BEq, DecidableEq

/--  denominator of Fixed p -/
structure Fixed.Denominator (precision : Nat) where
  val : Nat
  lt : val < 10 ^ precision
  deriving Repr, BEq, DecidableEq

/--  parts of Fixed p -/
structure Fixed.Parts (precision : Nat) where
  sign : Sign
  numerator : Nat
  denominator : Nat
  lt : denominator < 10 ^ precision
  deriving Repr, BEq, DecidableEq

def Fixed.zero : (Fixed p) := ⟨0⟩

def Fixed.Denominator.zero : (Fixed.Denominator p) := ⟨0, (Int.pos_pow_of_pos _ (by omega))⟩

instance : Inhabited (Fixed p) where
  default := Fixed.zero

instance {p} : LT (Fixed p) where
  lt a b := LT.lt a.val b.val

theorem lt_def (a b : Fixed p) : (a < b) = LT.lt a.val b.val := rfl

instance {p} : LE (Fixed p) where
  le a b := LE.le a.val b.val

instance {p} : LeRefl (Fixed p) where
  le_refl a := LeRefl.le_refl a.val

theorem le_def (a b : Fixed p) : (a ≤ b) = LE.le a.val b.val := rfl

instance : Inhabited (Fixed.Denominator p) where
  default := Fixed.Denominator.zero

theorem inhabited_def : (default : Fixed.Denominator p) = Fixed.Denominator.zero := rfl

instance {p} : LT (Fixed.Denominator p) where
  lt a b := LT.lt a.val b.val

instance {p} : LE (Fixed.Denominator p) where
  le a b := LE.le a.val b.val

instance {p} : LeRefl (Fixed.Denominator p) where
  le_refl a := LeRefl.le_refl a.val

namespace Fixed

def neg (f : Fixed p) : Fixed p :=
  ⟨-f.val⟩

def toParts (f : Fixed p) : Fixed.Parts p :=
  let n := f.val.natAbs
  let pow_p := 10 ^ p
  let n' := n / pow_p
  have h1 : 0 < (pow_p : Int) := Int.ofNat_lt.mpr (Int.pos_pow_of_pos _ (by omega))
  have h2 : n % pow_p < pow_p := Int.toNat_lt_toNat (Int.emod_lt_of_pos n h1) h1
  ⟨if f.val < 0 then .Neg else .Nonneg, n', n % pow_p, h2⟩

def toFixed (sign : Sign) (num : Nat) (denom : Fixed.Denominator p) : Fixed p :=
  ⟨match sign with
  | .Neg => Int.negOfNat (num * (10 ^ p) + denom.val)
  | .Nonneg => num * (10 ^ p) + denom.val⟩

def Parts.fromParts (parts : Fixed.Parts p) : Fixed p :=
  toFixed parts.sign parts.numerator ⟨parts.denominator, parts.lt⟩

def toSign (n : Int) : Sign :=
  if n < 0 then Sign.Neg else Sign.Nonneg

def toDenominator (n : Nat) (p : Nat) (h : n < 10 ^ p) : Fixed.Denominator p :=
  ⟨n, h⟩

def denominatorValueToString (d : Int) (p : Nat) : String :=
    let dropped := (toZeroPadded d p).toSubstring.dropRightWhile (λ c => c == '0')
    let s := dropped.toString
    if s != "" then "." ++ s else s

def denominatorToString (f : Fixed p) : String :=
    let ⟨_, _, d, _⟩  := toParts f
    denominatorValueToString d p

instance : ToString (Fixed p) where
  toString f :=
    let ⟨s, n, d, _⟩  := toParts f
    let sign := if s == .Neg then "-" else ""
    if d != 0 then s!"{sign}{n}{denominatorValueToString d p}" else s!"{n}"

def sub (dt1 dt2 : Fixed p) : Fixed p :=
  ⟨dt1.val - dt2.val⟩

def add (dt1 dt2 : Fixed p) : Fixed p :=
  ⟨dt1.val + dt2.val⟩

instance : Sub (Fixed p) where
  sub := sub

theorem sub_def (a b : Fixed p) : a - b = sub a b := rfl

instance : Add (Fixed p) where
  add := add

theorem add_def (a b : Fixed p) : a + b = add a b := rfl

def Int.toFixed (n : Int) (p : Nat) : Fixed p := ⟨n⟩

def div (dt1 dt2 : Fixed p) : Int :=
  dt1.val / dt2.val

instance : HDiv (Fixed p) (Fixed p) Int where
  hDiv := div

theorem div_def (a b : Fixed p) : a / b = div a b := rfl

def mul (a : Int) (f: Fixed p) : Fixed p :=
  ⟨a * f.val⟩

instance : HMul Int (Fixed p) (Fixed p) where
  hMul := mul

theorem mul_def (a : Int) (b : Fixed p) : a * b = mul a b := rfl

def mod (dt1 dt2 : Fixed p) : Fixed p :=
  ⟨dt1.val % dt2.val⟩

instance : Mod (Fixed p) where
  mod := mod

theorem mod_def (a b : Fixed p) : a % b = mod a b := rfl

@[simp] theorem ofFixed_lt {a b : Fixed p} : a < b ↔ a.val < b.val :=
  ⟨fun h => by simp only [LT.lt] at h; apply h,
  fun h => by simp only [LT.lt]; simpa⟩

@[simp] theorem ofFixed_ne {a b : Fixed p} : a ≠ b ↔ a.val ≠ b.val :=
  ⟨fun h => by simp [Fixed.ext_iff] at h; simpa,
  fun h => by simp [Fixed.ext_iff]; simpa⟩

theorem ne_of_lt {a b : Fixed p} (h : a < b) : a ≠ b := by
  exact ofFixed_ne.2 <| Int.ne_of_lt <| ofFixed_lt.1 h

theorem emod_nonneg (a : Fixed p) {b : Fixed p} (h : b ≠ ⟨0⟩) : ⟨0⟩ ≤ a % b := by
  have : 0 ≤ a.val % b.val := Int.emod_nonneg a.val (ofFixed_ne.1 h)
  simpa

theorem emod_lt_of_pos (a : Fixed p) {b : Fixed p} (h : ⟨0⟩ < b) : a % b < b := by
  have : a.val % b.val < b.val := Int.emod_lt_of_pos a.val (ofFixed_lt.1 h)
  simpa

theorem emod_add_ediv (a b : Fixed p) : a % b + (a / b) * b = a := by
  simp [mod_def, div_def, add_def]
  simp [Fixed.add, Fixed.mod, Fixed.div]
  simp [Fixed.ext_iff]
  exact Int.emod_add_ediv' a.val b.val

/-- toMod computes n % d : { m : Fixed p // zero ≤ m ∧ m < d } -/
def toMod (n d : Fixed p) (h : zero < d) : { m // zero ≤ m ∧ m < d } :=
  ⟨(n % d), And.intro
    (Fixed.emod_nonneg n (Ne.symm <| ne_of_lt <| ofFixed_lt.1 h))
    (Fixed.emod_lt_of_pos n h)⟩

private theorem toFixed_eq_zero (p : Nat)
    : (toFixed Sign.Nonneg 0 default : Fixed p) = Fixed.zero := by
  simp [Fixed.toFixed, Fixed.zero, inhabited_def, Fixed.Denominator.zero]

private theorem toFixed_of_ge_zero (p : Nat) (n : Nat) (denom :  Fixed.Denominator p)
    : (toFixed Sign.Nonneg n denom : Fixed p) = ⟨n * (10 ^ p) + denom.val⟩ := by
  simp [toFixed]

private theorem toFixed_of_lt_zero (p : Nat) (n : Nat) (denom :  Fixed.Denominator p)
    : (toFixed Sign.Neg n denom : Fixed p) =
    ⟨Int.negOfNat (Int.natAbs  n * (10 ^ p) + denom.val)⟩  := by
  simp [toFixed]

private theorem pos_pow_of_pos_cast {n : Nat} (m : Nat) (h : 0 < n) : 0 < (n:Int) ^ m := by
  have hp : 0 < n ^ m := @Int.pos_pow_of_pos n m h
  have : ((n ^ m : Nat) : Int) = (n : Int) ^ m := Int.natCast_pow n m
  rw [← this]
  exact Int.ofNat_le.mpr hp

theorem toFixed_lt_toFixed (p : Nat) (n : Nat) (n_denom : Fixed.Denominator p)
    (m : Nat) (m_denom : Fixed.Denominator p) (hnm : n < m) :
    (toFixed Sign.Nonneg n n_denom : Fixed p) < (toFixed Sign.Nonneg m m_denom : Fixed p) := by
  rw [toFixed_of_ge_zero _ _ _, toFixed_of_ge_zero  _ _ _]
  simp

  have h1 : (n : Int) * (10 ^ p) + n_denom.val < (n + 1) * (10 ^ p) :=
  by
    have h1 : (n : Int) * (10 ^ p) + (10 ^ p) = (n + 1) * (10 ^ p) := by simp [Int.add_mul]
    have h2 : (n : Int) * (10 ^ p) + n_denom.val < n * (10 ^ p) + (10 ^ p) := by
      have : (n_denom.val : Int) < (10 ^ p : Int) := by
        have : ((10 ^ p : Nat) : Int) = (10 : Int) ^ p := Int.natCast_pow 10 p
        rw [←this]
        exact Int.ofNat_lt.2 n_denom.lt
      refine Int.add_lt_add_left (this) ((n : Int) * 10 ^ p)
    rw [← h1]
    exact h2

  have h2 : ((n : Int) + 1) * (10 ^ p) ≤ m * (10 ^ p) := by
    have : (0 : Int) ≤ (10 : Int) ^ p := Int.le_of_lt <| @pos_pow_of_pos_cast 10 p (by omega)
    refine Int.mul_le_mul (by omega) (Int.le_of_eq (by simp)) this (by omega)

  have h3 : (m : Int) * (10 ^ p) ≤ m * (10 ^ p) + m_denom.val := by omega

  exact Int.lt_of_lt_of_le (Int.lt_of_lt_of_le h1 h2) h3

theorem zero_lt_toFixed (p : Nat) (m : Nat) (m_denom : Fixed.Denominator p) (h : 0 < m)
    : Fixed.zero < (toFixed Sign.Nonneg m m_denom : Fixed p) := by
  have : toFixed Sign.Nonneg 0 default < (toFixed Sign.Nonneg m m_denom : Fixed p) :=
    toFixed_lt_toFixed p _ _ m m_denom h
  rw [← toFixed_eq_zero p]
  simp [this]

theorem toFixed_le_toFixed_of_lt (p : Nat) (n : Nat) (n_denom : Fixed.Denominator p)
    (m : Nat) (m_denom : Fixed.Denominator p) (hnm : n < m) :
    (toFixed Sign.Nonneg n n_denom : Fixed p) ≤ (toFixed Sign.Nonneg m m_denom : Fixed p) := by
  have h1 : (toFixed Sign.Nonneg n n_denom : Fixed p).val
      < (toFixed Sign.Nonneg m m_denom : Fixed p).val :=
    toFixed_lt_toFixed p n n_denom m m_denom hnm
  have h2 : (toFixed Sign.Nonneg n n_denom : Fixed p).val
      ≤ (toFixed Sign.Nonneg m m_denom : Fixed p).val := by
    simp [Int.le_of_lt h1]
  exact h2

theorem zero_le_toFixed (p : Nat) (m : Nat) (m_denom : Fixed.Denominator p) (hnm : 0 < m)
    : Fixed.zero ≤ (toFixed Sign.Nonneg m m_denom : Fixed p) := by
  have : toFixed Sign.Nonneg 0 default < (toFixed Sign.Nonneg m m_denom : Fixed p) :=
    toFixed_lt_toFixed p _ _ m m_denom hnm
  have : toFixed Sign.Nonneg 0 default ≤ (toFixed Sign.Nonneg m m_denom : Fixed p) := by
    have h : (toFixed Sign.Nonneg 0 default : Fixed p).val
        ≤ (toFixed Sign.Nonneg m m_denom : Fixed p).val := by
      simp [Int.le_of_lt this]
    exact h
  rw [← toFixed_eq_zero p]
  simp [this]

private theorem le_of_div_pow (val : Int) (p : Nat) (h : 0 ≤ val)
    : 0 ≤ val / (((10 ^ p) : Nat) : Int) := by
  have : 0 ≤ (((10 ^ p) : Nat) : Int) :=
    Int.le_of_lt <| Int.ofNat_lt.mpr <| Int.pos_pow_of_pos _ (by omega)
  rw [← Int.tdiv_eq_ediv h this]
  simp [Int.tdiv_nonneg h this]

theorem fixed_eq_toParts_fromParts (f : Fixed p) : f = f.toParts.fromParts := by
  simp [Fixed.toParts, Parts.fromParts, toFixed]
  split <;> simp_all
  · rename_i h
    simp [Int.negOfNat]
    split <;> try simp_all
    · rename_i heq
      simp [Int.natAbs] at heq
      split at heq <;> simp_all
      · omega
      · rename_i n _
        rewrite [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heq.2)] at heq
        have := heq.1
        contradiction
    · rename_i m heq
      have : Int.natAbs f.val / 10 ^ p * 10 ^ p + Int.natAbs f.val % 10 ^ p = Int.natAbs f.val := by
        rw [Nat.mul_comm]
        apply Nat.div_add_mod (Int.natAbs f.val) (10 ^ p)
      rw [this] at heq
      have hm : f.val = -(m + 1 : Int) := by omega
      have hf : Int.negSucc m = f.val := by rw [hm, (Int.negSucc_eq m)]
      rw [hf]
  · rename_i h
    have : ¬¬f.val < 0 ↔ f.val < 0 := Classical.not_not
    rw [← this] at h
    have hf : Int.natAbs f.val = f.val := by omega
    rw [hf]
    have : ((10 ^ p : Nat) : Int) = (10 : Int) ^ p := Int.natCast_pow 10 p
    rw [this]
    have : f.val / (10 ^ p : Int) * 10 ^ p + f.val % (10 ^ p) = f.val := by
      rw [Int.add_comm]
      exact Int.emod_add_ediv' f.val (10 ^ p)
    rw [this]
