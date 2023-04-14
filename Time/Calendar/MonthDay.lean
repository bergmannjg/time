import Mathlib.Tactic.NormNum
import Time.Calendar.Private

namespace Time

open Private

def monthLengths (isleap : Bool) :=
  [ (1, 31), (2, if isleap then 29 else 28), (3, 31), (4, 30), (5, 31),
    (6, 30), (7, 31), (8, 31), (9, 30), (10, 31), (11, 30), (12, 31)]

theorem monthLengths_length_eq_12 (isleap : Bool) : (monthLengths isleap).length == 12 := by
  cases isleap <;> norm_num

theorem monthLengths_month_le_12 (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.1 ∧ a.1 ≤ 12 := by
  cases isleap <;> simp

theorem monthLengths_days_ge_28 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), 28 <= a.2 := by
  cases isleap <;> simp

theorem monthLengths_days_le_31 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), a.2 <= 31 := by
  cases isleap <;> norm_num

theorem monthLengths_mem_in_icc (isleap : Bool) : ∀ a ∈ (monthLengths isleap), a.2 ∈ Set.Icc 28 31
  := by cases isleap <;> norm_num

private def findMonthDay (monthLengths : List (Nat × Nat)) (m : Nat) (yd : Nat)
    (hmonth : ∀ a ∈ monthLengths, 1 ≤ a.1 ∧ a.1 <= 12)
    (hdays : ∀ a ∈ monthLengths, a.2 <= 31) (hy : 1 <= yd)
    :  Set.Icc 1 12 × Set.Icc 1 31 :=
  match monthLengths with
  | ((ml, n) :: ns) =>
      if h1 : yd <= n
      then
        have hm : 1 ≤ ml ∧ ml ≤ 12 := by simp_all only [List.mem_cons, forall_eq_or_imp,
          Prod.forall, and_self]
        have hn : n <= 31 := by simp_all only [List.mem_cons, forall_eq_or_imp]
        have hn' : yd <= 31 := Nat.le_trans h1 hn
        (⟨ml, hm⟩, ⟨yd, And.intro hy hn'⟩)
      else
        have hmonth' : ∀ a ∈ ns, 1 ≤ a.1 ∧ a.1 <= 12 := (List.forall_mem_cons.mp hmonth).right
        have hdays' : ∀ a ∈ ns, a.2 <= 31 := (List.forall_mem_cons.mp hdays).right
        have hy' : 0 < yd - n := by simp_all only [not_le, ge_iff_le, tsub_pos_iff_lt]
        findMonthDay ns (m + 1) (yd - n) hmonth' hdays' hy'
  | _ => (⟨1, (by simp)⟩, ⟨1, (by simp)⟩)

def dayOfYearToMonthAndDay (isLeap : Bool) (yd : Set.Icc 1 366)
    : Set.Icc 1 12 × Set.Icc 1 31 :=
  let ml := monthLengths isLeap
  have hmonth : ∀ a ∈ ml, 1 ≤ a.1 ∧ a.1 <= 12 := monthLengths_month_le_12 isLeap
  have hdays : ∀ a ∈ ml, a.2 <= 31 := monthLengths_days_le_31 isLeap
  findMonthDay ml 1 yd.val hmonth hdays yd.property.left

/-- The length of a given month in the Gregorian or Julian calendars. -/
def monthLength' (isLeap : Bool) (month': Fin 12) :=
  ((monthLengths isLeap).get month').2

theorem monthLength'_ge_1 (isLeap : Bool) (month': Fin 12)
   : 1 <= monthLength' (isLeap : Bool) (month': Fin 12) := by
  simp only [monthLength']
  have h1 : 1 ≤ 28 := by norm_num1
  have h : List.get (monthLengths _) _ ∈ monthLengths _ :=
    List.get_mem (monthLengths isLeap) month'.val month'.isLt
  have h2: 28 <= monthLength' _ _ := monthLengths_days_ge_28 _ _ h
  exact Nat.le_trans h1 h2

theorem monthLength'_le_31 (isLeap : Bool) (month': Fin 12)
   : monthLength' (isLeap : Bool) (month': Fin 12) <= 31 := by
  simp only [monthLength']
  have h : List.get (monthLengths _) _ ∈ monthLengths _ :=
    List.get_mem (monthLengths isLeap) month'.val month'.isLt
  exact monthLengths_days_le_31 _ _ h

theorem monthAndDayToDayOfYear_gt_zero_of_month_gt (month day k : Int)
    (hm : 2 < month) (hk : -2 ≤ k) (hd : 0 < day)
    : 0 < ((367 * month - 362) / 12 + k) + day := by
  let y := 367 * month - 362

  have ha : 0 ≤ y / 12 + k := by
    have h1 : 0 <= 2 + k := Int.add_le_add_left hk _
    have h2 : 2 <= y / 12 := by
      let x : Int := 12 * 2
      have h1 : x + 362 < 367 * 2 := by norm_num
      have h2 : x + 362 < 367 * month := by
        simp [Int.lt_trans h1 (Int.mul_lt_mul_of_pos_left hm (by simp))]
      have h3 : x <= y := by simp [Int.le_of_lt (Int.lt_sub_right_of_add_lt h2)]
      exact (Int.le_ediv_iff_mul_le (by simp only)).mpr h3
    have h3 : 2 + k <= y / 12 + k := by
      exact Int.add_le_add_right h2 k
    simp [Int.le_trans h1 h3]

  simp [Int.add_pos_of_nonneg_of_pos ha hd]

theorem monthAndDayToDayOfYear_le (month day k : Int)
    (hm : month ≤ 12) (hk : k = -2 ∨ k = -1) (hd2 : day ≤ 31)
    : ((367 * month - 362) / 12 + k) + day ≤ 366 := by
  have h1 : 367 * month ≤ 367 * 12 := Int.mul_le_mul_of_nonneg_left hm (by simp)
  have h2 : 367 * month - 362 ≤ 367 * 12 - 362 := Int.sub_le_sub_right h1 _
  have h3 : (367 * month - 362) / 12 ≤ (367 * 12 - 362) / 12 := Int.ediv_le_ediv (by simp) h2
  apply Or.elim hk
  · intro hq
    have h4 : (367 * month - 362) / 12 + k ≤ (367 * 12 - 362) / 12 - 2 := by aesop
    have h5 : ((367 * month - 362) / 12 + k) + day ≤ (367 * 12 - 362) / 12 - 2 + 31 :=
      Int.add_le_add h4 hd2
    have h6 : (367 * 12 - 362) / 12 - 2 + 31 ≤ 365 := by norm_num
    exact Int.le_trans h5 (Int.ofNat_le_ofNat_of_le (Nat.le_trans h6 (Nat.le_succ 365)))
  · intro hq
    have h4 : (367 * month - 362) / 12 + k ≤ (367 * 12 - 362) / 12 - 1 := by aesop
    have h5 : ((367 * month - 362) / 12 + k) + day ≤ (367 * 12 - 362) / 12 - 1 + 31 :=
      Int.add_le_add h4 hd2
    have h6 : (367 * 12 - 362) / 12 - 1 + 31 ≤ 366 := by norm_num
    exact Int.le_trans h5 (Int.ofNat_le_ofNat_of_le h6)

private def monthAndDayToDayOfYearClipped_month_le (isLeap : Bool) (month : Nat)
    (day : Nat) (hd1 : 1 <= day) (hd2 : day ≤ 31) (h : month <= 2) : Set.Icc 1 366 :=
  let k := 0
  let x := ((367 * month - 362) / 12 + k) + day

  have h1 : 0 < x := by
    have : 0 < day := by exact hd1
    exact add_pos_iff.mpr (Or.inr this)

  have h2 : x ≤ 366 := by
    have h1 : x ≤ (367 * 2 - 362) / 12 + 31 := by
      have : (367 * month - 362) / 12 ≤ (367 * 2 - 362) / 12 :=
        Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ h) _)
      have h : (367 * month - 362) / 12 + k ≤ (367 * 2 - 362) / 12 := by simpa
      exact Nat.add_le_add h hd2

    exact Nat.le_trans h1 (by norm_num)

  ⟨x, And.intro h1 h2⟩

private def monthAndDayToDayOfYearClipped_month_gt (isLeap : Bool) (month' : NonemptyIcc 1 12)
    (day' : Nat) (hd1 : 1 <= day') (hd2 : day' ≤ 31) (h : 2 < month'.icc.val) : Set.Icc 1 366 :=
  let k : Int := if isLeap then -1 else -2
  let month : Int := month'.icc.val
  let day : Int := day'
  let x := ((367 * month - 362) / 12 + k) + day

  have hx1 : 0 < x := by
    have h1 : 2 <  month := Int.ofNat_lt.mpr h
    have h2 : -2 ≤ if isLeap then -1 else -2 := by aesop
    have h3 : 0 < day := by
      have ha : 0 < day' := by exact hd1
      exact Int.ofNat_lt.2 ha
    exact monthAndDayToDayOfYear_gt_zero_of_month_gt month day k h1 h2 h3

  let x' := Int.toNat x

  have hx1' : 0 < x' := by
    simp_all only [not_le, Int.lt_toNat, Nat.cast_zero]

  have hx2 : x ≤ 366 := by
    have hk : k = -2 ∨ k = -1 := by aesop
    have hm : month ≤ 12 := Int.ofNat_le_ofNat_of_le month'.icc.property.right
    have hd2' : day ≤ 31 := Int.ofNat_le_ofNat_of_le hd2
    exact monthAndDayToDayOfYear_le month day k hm hk hd2'

  have hx2' : x' ≤ 366 := by
    simp_all only [Int.lt_toNat, Nat.cast_zero, Int.toNat_le, Nat.cast_ofNat]

  ⟨x', And.intro hx1' hx2'⟩

private def monthAndDayToDayOfYearClipped (isLeap : Bool) (month' : NonemptyIcc 1 12)
    (day' : Nat) (hd1 : 1 <= day') (hd2 : day' ≤ 31) : Set.Icc 1 366 :=
  if h : month'.icc.val <= 2 then
    monthAndDayToDayOfYearClipped_month_le isLeap month'.icc.val day' hd1 hd2 h
  else
    monthAndDayToDayOfYearClipped_month_gt isLeap month' day' hd1 hd2 (not_le.mp h)

theorem days_le_31 (isLeap : Bool) (m : Fin 12) (day : NonemptyIcc 1 (monthLength' isLeap m))
    : day.icc.val ≤ 31 :=
  have h1 : day.icc.val ≤  monthLength' isLeap m := day.icc.property.right
  have h2 : monthLength' isLeap m ≤ 31 := monthLength'_le_31 isLeap m
  Nat.le_trans h1 h2

/-- Convert month and day in the Gregorian or Julian calendars to day of year. -/
def monthAndDayToDayOfYear (isLeap : Bool) (month : Int) (day : Int) :  Set.Icc 1 366 :=
  let month' := clip' 1 12 month (by simp)
  let month'' : Fin 12 := month'
  let day' := clip' 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  monthAndDayToDayOfYearClipped isLeap month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')

/-- Convert month and day in the Gregorian or Julian calendars to day of year option. -/
def monthAndDayToDayOfYearValid (isLeap : Bool) (month : Int) (day : Int)
    : Option  $ Set.Icc 1  366 := do
  let month' ← clipValid' 1 12 month (by simp)
  let month'' : Fin 12 :=  month'
  let day' ← clipValid' 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  return monthAndDayToDayOfYearClipped isLeap month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')
