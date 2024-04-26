import Init.Data.Int.Order
import Std.Data.List.Lemmas
import Time.Data.Int.Order
import Time.Calendar.OrdinalDate

namespace Time

open Clip

def monthLengths (isleap : Bool) :=
  [ (1, 31), (2, if isleap then 29 else 28), (3, 31), (4, 30), (5, 31),
    (6, 30), (7, 31), (8, 31), (9, 30), (10, 31), (11, 30), (12, 31)]

def monthLengths' (isleap : Bool) :=
  (monthLengths isleap).lookup

/--  Date in proleptic Gregorian calendar. -/
structure Date where
  Year : Int
  Month : Time.Icc 1 12
  Day : Time.Icc 1 31
  IsValid : ∃ m ∈ monthLengths (isLeapYear Year), m.1 = Month.val ∧ Day.val ≤ m.2
  deriving Repr

namespace Time.Notation

/-- Date syntactic category -/
declare_syntax_cat date
/-- Date from numeric literals year, month and day -/
syntax num noWs "-" noWs num noWs "-" noWs num : date
syntax "date%" date : term

/--
  `date% year-month-day` is notation for
  `Time.Date.mk year ⟨month, by omega⟩ ⟨day, by omega⟩ (by native_decide)`
  for the numeric literals year, month and day.
-/
macro_rules
| `(date% $y:num-$m:num-$d:num) =>
    `(Time.Date.mk $y ⟨$m, by omega⟩ ⟨$d, by omega⟩ (by native_decide))

end Time.Notation

instance : BEq Date where
  beq a b := decide (Eq a.Year b.Year) && decide (Eq a.Month.val b.Month.val) && decide (Eq a.Day.val b.Day.val)

instance : Inhabited Date where
  default := date% 1-1-1

def monthLengths_sum (isleap : Bool) : Nat :=
  (monthLengths isleap).foldl (fun acc m => acc + m.2) 0

theorem monthLengths_sum_eq (isleap : Bool) :
  monthLengths_sum isleap == if isleap then 366 else 365 := by
  cases isleap <;> simp_arith

theorem monthLengths_length_eq_12 (isleap : Bool) : (monthLengths isleap).length == 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_length_gt_0 (isleap : Bool) : 0 < (monthLengths isleap).length := by
  cases isleap <;> simp_arith

theorem monthLengths_month_in (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.1 ∧ a.1 ≤ 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_in (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.2 ∧ a.2 ≤ 31 := by
  cases isleap <;> simp_arith

theorem list_foldl_init_add (l : List α) (init v : Nat) (f : α → Nat)
  : List.foldl (fun acc v => f v + acc) init l + v
    = List.foldl (fun acc v => f v + acc) (init + v) l := by
  induction l generalizing init with
  | nil =>
    unfold List.foldl
    simp_all
  | cons h t ih =>
    unfold List.foldl
    simp [*]
    have : List.foldl (fun acc v => f v + acc) (f h + init + v) t
              = List.foldl (fun acc v => f v + acc) ((f h + init) + v) t := by
      simp [ih]
    have hy : List.foldl (fun acc v => f v + acc) ((f h + init) + v) t
              = List.foldl (fun acc v => f v + acc) (f h + (init + v)) t := by
      have : (f h + init) + v = f h + (init + v) := by simp_arith
      rw [this]
    rw [hy]

private def findValidMonthDay (year : Int) (l : List (Nat × Nat)) (v sum : Nat)
    (h1 : l.foldl (fun acc v => v.2 + acc) 0 = sum) (h2 : v ≤ sum) (h3 : 1 ≤ v)
    (h4 : ∃ s : List (Nat × Nat), monthLengths (isLeapYear year) = s ++ l) (_ : l ≠ [])
    (h6 : ∀ a ∈ l, 1 ≤ a.1 ∧ a.1 ≤ 12)
    (h7 : ∀ a ∈ l, 1 ≤ a.2 ∧ a.2 ≤ 31)
    : Date :=
  let isLeap := isLeapYear year
  match l with
  | b :: l' =>
    if h : v ≤ b.2
    then
      ⟨year, ⟨b.1, by simp [h6]⟩,
        ⟨v, by
          specialize h7 b
          simp_all [h7]
          exact Nat.le_trans h h7.right
        ⟩, by
          exists b
          specialize h7 b
          obtain ⟨s, h4'⟩ := h4
          simp_all [List.mem_append.mpr _]⟩
    else
      let sum' := sum - b.2
      let v' := v - b.2
      have h' : b.2 < v := Nat.lt_of_not_ge h
      have h3' : 0 < v' := Nat.zero_lt_sub_of_lt h'
      have h2' : v' ≤ sum' := by
        have hsum : sum' = sum - b.2 := by simp
        rw [hsum]
        have hv : v' = v - b.2 := by simp
        rw [hv]
        apply Nat.sub_le_sub_right h2 b.2
      have h1' : l'.foldl (fun acc v => v.2 + acc) 0 = sum' := by
        unfold List.foldl at h1
        have hx : List.foldl (fun acc v => v.2 + acc) 0 l' + b.2
                  = List.foldl (fun acc v => v.2 + acc) (b.2 + 0) l' := by
          simp [list_foldl_init_add l' 0 b.2 _]
        rw [← hx] at h1
        --simp_all
        have hx' : sum = List.foldl (fun acc v => v.2 + acc) 0 l' + b.2 := by
          simp_all
        simp [sum']
        simp [Nat.sub_eq_of_eq_add hx']
      have h4' : ∃ s' : List (Nat × Nat), monthLengths isLeap = s' ++ l' := by
          obtain ⟨s, h4'⟩ := h4
          exists s ++ [b]
          simp_all
      have h5' : l' ≠ [] := by
        have hx : 0 < sum' := Nat.lt_of_lt_of_le h3' h2'
        have : 0 < l'.foldl (fun acc v => v.2 + acc) 0 := by
          rw [h1']
          simp_all [hx]
        match hm : l' with
        | [] => simp_all
        | _ :: _ => simp_all
      have h6' : ∀ a ∈ l', 1 ≤ a.1 ∧ a.1 ≤ 12 := (List.forall_mem_cons.mp h6).right
      have h7' : ∀ a ∈ l', 1 ≤ a.2 ∧ a.2 ≤ 31 := (List.forall_mem_cons.mp h7).right
      findValidMonthDay year l' v' sum' h1' h2' h3' h4' h5' h6' h7'

private def findMonthDayCommon (year : Int) (yd : Time.Icc 1 365) (h : (isLeapYear year) = false)
    : Date :=
  findValidMonthDay year (monthLengths (isLeapYear year)) yd.val 365
      (by
        have : monthLengths_sum false == 365 := monthLengths_sum_eq false
        unfold monthLengths_sum at this
        simp_all
        exact this)
      (by simp [yd.property.right])
      (by simp [yd.property.left])
      ⟨[], rfl⟩
      (by simp [List.length_pos.mp (monthLengths_length_gt_0 (isLeapYear year))])
      (monthLengths_month_in (isLeapYear year))
      (monthLengths_days_in (isLeapYear year))

private def findMonthDayLeap (year : Int) (yd : Time.Icc 1 366) (h : (isLeapYear year) = true)
    : Date :=
  findValidMonthDay year (monthLengths (isLeapYear year)) yd.val 366
      (by
        have : monthLengths_sum true == 366 := monthLengths_sum_eq true
        unfold monthLengths_sum at this
        simp_all
        exact this)
      (by simp [yd.property.right])
      (by simp [yd.property.left])
      ⟨[], rfl⟩
      (by simp [List.length_pos.mp (monthLengths_length_gt_0 (isLeapYear year))])
      (monthLengths_month_in (isLeapYear year))
      (monthLengths_days_in (isLeapYear year))

def ordinalDateToDate (dt : OrdinalDate) : Date :=
  match h : dt.dayOfYear with
  | .common yd => findMonthDayCommon dt.year yd (by
      have hx : match dt.dayOfYear with
            | .common _ => isLeapYear dt.year = false
            | .leap _ => isLeapYear dt.year = true := dt.isValid
      split at hx <;> simp_all)
  | .leap yd => findMonthDayLeap dt.year yd (by
      have hx : match dt.dayOfYear with
            | .common _ => isLeapYear dt.year = false
            | .leap _ => isLeapYear dt.year = true := dt.isValid
      split at hx <;> simp_all)

theorem monthLengths_month_le_12 (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.1 ∧ a.1 ≤ 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_ge_28 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), 28 <= a.2 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_le_31 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), a.2 <= 31 := by
  cases isleap <;> simp_arith

/-
theorem monthLengths_mem_in_icc (isleap : Bool) : ∀ a ∈ (monthLengths isleap), a.2 ∈ Time.Icc 28 31
  := by cases isleap <;> simp_arith
-/

/-- The length of a given month in the Gregorian or Julian calendars. -/
def monthLength' (isLeap : Bool) (month': Fin 12) :=
  ((monthLengths isLeap).get month').2

theorem monthLength'_ge_1 (isLeap : Bool) (month': Fin 12)
   : 1 <= monthLength' (isLeap : Bool) (month': Fin 12) := by
  simp only [monthLength']
  have h1 : 1 ≤ 28 := by omega
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
    have h2 : 2 + k <= y / 12 + k := by omega
    simp [Int.le_trans h1 h2]

  simp [Int.add_pos_of_nonneg_of_pos ha hd]

theorem monthAndDayToDayOfYear_le (month day k : Int)
    (hm : month ≤ 12) (hk : k = -2 ∨ k = -1) (hd2 : day ≤ 31)
    : ((367 * month - 362) / 12 + k) + day ≤ 366 := by
  omega

private def monthAndDayToDayOfYearClipped_month_le (isLeap : Bool) (month : Nat)
    (day : Nat) (hd1 : 1 <= day) (hd2 : day ≤ 31) (h : month <= 2) : Time.Icc 1 366 :=
  let k := 0
  let x := ((367 * month - 362) / 12 + k) + day
  ⟨x, And.intro (by omega) (by omega)⟩

private def monthAndDayToDayOfYearClipped_month_gt (isLeap : Bool) (month' : NonemptyIcc 1 12)
    (day' : Nat) (hd1 : 1 <= day') (hd2 : day' ≤ 31) (h : 2 < month'.icc.val) : Time.Icc 1 366 :=
  let k : Int := if isLeap then -1 else -2
  let month : Int := month'.icc.val
  let day : Int := day'
  let x := ((367 * month - 362) / 12 + k) + day

  have hx1 : 0 < x := by omega

  let x' := Int.toNat x

  have hx1' : 0 < x' := Int.lt_toNat hx1 (by omega)

  have hx2 : x ≤ 366 := by
    have hk : k = -2 ∨ k = -1 := by cases isLeap <;> simp [k]
    have hm : month ≤ 12 := Int.ofNat_le.2 month'.icc.property.right
    have hd2' : day ≤ 31 := Int.ofNat_le.2 hd2
    exact monthAndDayToDayOfYear_le month day k hm hk hd2'

  have hx2' : x' ≤ 366 := Int.toNat_le hx2

  ⟨x', And.intro hx1' hx2'⟩

private def monthAndDayToDayOfYearClipped (isLeap : Bool) (month' : NonemptyIcc 1 12)
    (day' : Nat) (hd1 : 1 <= day') (hd2 : day' ≤ 31) : Time.Icc 1 366 :=
  if h : month'.icc.val <= 2 then
    monthAndDayToDayOfYearClipped_month_le isLeap month'.icc.val day' hd1 hd2 h
  else
    monthAndDayToDayOfYearClipped_month_gt isLeap month' day' hd1 hd2 (by omega)

theorem days_le_31 (isLeap : Bool) (m : Fin 12) (day : NonemptyIcc 1 (monthLength' isLeap m))
    : day.icc.val ≤ 31 :=
  have h1 : day.icc.val ≤  monthLength' isLeap m := day.icc.property.right
  have h2 : monthLength' isLeap m ≤ 31 := monthLength'_le_31 isLeap m
  Nat.le_trans h1 h2

/-- Convert month and day in the Gregorian or Julian calendars to day of year. -/
def monthAndDayToDayOfYear (isLeap : Bool) (month : Int) (day : Int) :  Time.Icc 1 366 :=
  let month' := clipToNonemptyIcc 1 12 month (by simp_arith)
  let month'' : Fin 12 := month'
  let day' := clipToNonemptyIcc 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  monthAndDayToDayOfYearClipped isLeap month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')

/-- Convert month and day in the Gregorian or Julian calendars to day of year option. -/
def monthAndDayToDayOfYearValid (isLeap : Bool) (month : Int) (day : Int)
    : Option  $ Time.Icc 1  366 := do
  let month' ← clipToNonemptyIcc? 1 12 month (by simp_arith)
  let month'' : Fin 12 :=  month'
  let day' ← clipToNonemptyIcc? 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  return monthAndDayToDayOfYearClipped isLeap month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')
