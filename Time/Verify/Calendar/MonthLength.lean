import Time
import Time.Data.List.Basic

/-!
## Theorems about `Time.monthLengths` properties
-/

namespace Verify.MonthLength

open Time

/-- Relation of Date to `Time.monthLengths` list. -/
@[simp] def monthLengthsOfDate (m : Nat × Nat) (dt : Date) :=
  m ∈ (monthLengths (isLeapYear dt.Year))
  ∧ m.fst = dt.Month.val ∧ dt.Day.val ≤ m.snd

/-- Build relation of Date to `Time.monthLengths`. -/
def monthLengths_of_date (dt : Date) : {m // monthLengthsOfDate m dt} :=
  let a := List.findExisting
     (fun m => m.fst = dt.Month.val ∧ dt.Day.val ≤ m.snd)
    (Time.monthLengths (isLeapYear dt.Year))
    (by
      simp
      let ⟨m, hm⟩ := dt.IsValid
      have : (_, _) ∈ monthLengths (isLeapYear dt.Year) := hm.left
      exact ⟨m.1, by exact ⟨m.2, hm⟩⟩)
  ⟨a.val, by
    have := a.property.right
    simp_all
    exact a.property.left⟩

theorem monthLengths_days_le (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), (if isleap then 29 else 28) ≤ a.2 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_days_sub_lt (isleap : Bool)
  : ∀ a ∈ (monthLastDayAsDayOfYear' isleap), a.2.1 < a.2.2 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_sub_le_31 (isleap : Bool)
    : ∀ a ∈ (monthLastDayAsDayOfYear' isleap), a.2.2 - a.2.1 ≤ 31 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_sub_of_monthLengths (isleap : Bool)
    : ∀ a b, a ∈ monthLastDayAsDayOfYear' isleap →  b ∈ monthLengths isleap
        → a.1 = b.1 → a.2.2 - a.2.1 + 1 = b.2 := by
  cases isleap <;> simp [monthLastDayAsDayOfYear', monthLengths] <;> omega

theorem monthLastDayAsDayOfYear'_snd_fst_lt (isleap : Bool)
    : ∀ a ∈ (monthLastDayAsDayOfYear' isleap), 0 < a.2.1 := by
  cases isleap <;> simp_arith

private theorem monthLastDayAsDayOfYear'_month_lt_12_lt_not (isleap : Bool)
    : ∀ a ∈ monthLastDayAsDayOfYear' isleap,
        ¬a.2.1 < (if isleap then 336 else 335) → ¬a.1 < 12 := by
  cases isleap <;> simp [monthLastDayAsDayOfYear']

theorem monthLastDayAsDayOfYear'_month_lt_12_lt (isleap : Bool) (dt : Date)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 < 12)
    : a.val.2.1 < if isleap then 336 else 335 := by
  by_contra
  have := monthLastDayAsDayOfYear'_month_lt_12_lt_not isleap a a.property.left (by omega)
  contradiction

theorem monthLastDayAsDayOfYear'_month_1_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.2.1 ≤ 31)
    : 1 = a.val.1 := by
  have ⟨i', h'⟩ := List.get_of_mem a.property.left
  have := monthLastDayAsDayOfYear'_fst_eq_of_le_31 isleap i' (by simp_all)
  simp_all

theorem monthLastDayAsDayOfYear'_day_of_month_1_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 1)
    : 1 = a.val.2.1 := by
  have ⟨i', h'⟩ := List.get_of_mem a.property.left
  have := monthLastDayAsDayOfYear'_snd_eq_of_eq_1 isleap i' (by simp_all)
  simp_all

theorem monthLastDayAsDayOfYear'_index_eq_if_fst_eq
  (i : Fin (monthLastDayAsDayOfYear' isleap).length)
  (i' : Fin (monthLengths isleap).length)
  (h : (monthLastDayAsDayOfYear' isleap)[i.val].fst = (monthLengths isleap)[i'.val].fst)
    : i.val = i'.val := by
  have := monthLastDayAsDayOfYear'_fst_eq isleap i
  rw [this] at h
  exact monthLengths_index_eq_of_fst_eq isleap i i' h

theorem monthLastDayAsDayOfYear'_sub_eq_incr (i : Fin (monthLastDayAsDayOfYear' isleap).length)
  (dt : Date)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hmonth : ((monthLastDayAsDayOfYear' isleap).get i).fst = dt.Month.val)
    : dt.Day.val = (monthLastDayAsDayOfYear' isleap)[i.val].snd.snd
                    - (monthLastDayAsDayOfYear' isleap)[i.val].snd.fst + 1 := by
  have ⟨i', h'⟩ := List.get_of_mem ml.property.left
  rw [hl] at h'
  have h'month : (monthLengths isleap)[i'.val].fst = dt.Month.val := by
    rw [← ml.property.right.left]
    simp_all
  have h'day : dt.Day.val = (monthLengths isleap)[i'.val].snd := by
    simp_all

  have := monthLastDayAsDayOfYear'_index_eq_if_fst_eq i i' (by simp_all)
  have h'day : dt.Day.val = (monthLengths isleap)[i.val].snd := by
    simp_all

  have := monthLastDayAsDayOfYear'_sub_eq isleap i
  simp_all

theorem monthLastDayAsDayOfYear'_sub_le (i : Fin (monthLastDayAsDayOfYear' isleap).length)
  (dt : Date)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hmonth : ((monthLastDayAsDayOfYear' isleap).get i).fst = dt.Month.val)
    : dt.Day.val ≤ (monthLastDayAsDayOfYear' isleap)[i].snd.snd
                    - (monthLastDayAsDayOfYear' isleap)[i].snd.fst := by
  have ⟨i', h'⟩ := List.get_of_mem ml.property.left
  rw [hl] at h'
  have h'month : (monthLengths isleap)[i'.val].fst = dt.Month.val := by
    rw [← ml.property.right.left]
    simp_all
  have h'day : dt.Day.val < (monthLengths isleap)[i'.val].snd := by
    simp_all

  have := monthLastDayAsDayOfYear'_index_eq_if_fst_eq i i' (by simp_all)
  have h'day : dt.Day.val < (monthLengths isleap)[i.val].snd := by
    simp_all

  have := monthLastDayAsDayOfYear'_sub_eq isleap i
  simp_all
  omega

theorem monthLastDayAsDayOfYear'_index_eq (i i' : Fin (monthLastDayAsDayOfYear' isleap).length)
  (dt : Date)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hmonth : ((monthLastDayAsDayOfYear' isleap).get i').fst = dt.Month.val)
  (h1 : (monthLastDayAsDayOfYear' isleap)[i].snd.fst
        ≤ (monthLastDayAsDayOfYear' isleap)[i'].snd.fst + dt.Day.val)
  (h2 : (monthLastDayAsDayOfYear' isleap)[i'].snd.fst + dt.Day.val
        ≤ (monthLastDayAsDayOfYear' isleap)[i].snd.snd)
    : i = i' := by
  have := dt.Day.property
  have : i.val ≤ i'.val := by
    have h := monthLastDayAsDayOfYear'_sub_le i' dt hl hml h hmonth
    have := monthLastDayAsDayOfYear'_fst_lt_snd isleap i'
    have : (monthLastDayAsDayOfYear' isleap)[i].snd.fst
           ≤ (monthLastDayAsDayOfYear' isleap)[i'].snd.snd := by omega
    exact monthLastDayAsDayOfYear'_index_le_of_fst_le_snd isleap i' i this
  have : i'.val ≤ i.val := by
    have : (monthLastDayAsDayOfYear' isleap)[i'].snd.fst
         < (monthLastDayAsDayOfYear' isleap)[i].snd.snd := by omega
    exact monthLastDayAsDayOfYear'_index_le_of_fst_lt_snd isleap i i' this
  omega

theorem monthLastDayAsDayOfYear'_index_eq_of_last_day_in_month
  (i i' : Fin (monthLastDayAsDayOfYear' isleap).length)
  (dt : Date)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hmonth : ((monthLastDayAsDayOfYear' isleap).get i').fst = dt.Month.val)
  (h1 : (monthLastDayAsDayOfYear' isleap)[i.val].snd.fst
        ≤ (monthLastDayAsDayOfYear' isleap)[i'.val].snd.fst + dt.Day.val)
  (h2 : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.fst + dt.Day.val
        ≤ (monthLastDayAsDayOfYear' isleap)[i.val].snd.snd)
    : i.val - 1 = i'.val := by
  have := monthLastDayAsDayOfYear'_sub_eq_incr i' dt hl hml h hmonth
  rw [this] at h1
  rw [this] at h2

  have : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.fst
          < (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd :=
    monthLastDayAsDayOfYear'_fst_lt_snd isleap i'

  have : i.val ≤  i'.val + 1 := by
    have h1 : (monthLastDayAsDayOfYear' isleap)[i.val].snd.fst
            ≤ (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd + 1 := by  omega
    exact monthLastDayAsDayOfYear'_index_le_of_fst_le_snd_incr isleap i' i h1

  have : i'.val + 1 ≤ i.val := by
    have h2 : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd + 1
            ≤ (monthLastDayAsDayOfYear' isleap)[i.val].snd.snd := by omega
    exact monthLastDayAsDayOfYear'_index_le_of_snd_le_snd_incr isleap i i' h2

  omega
