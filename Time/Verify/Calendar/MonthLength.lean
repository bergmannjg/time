import Time
import Time.Data.List.Basic

/-!
## Theorems about `Time.monthLengths` properties
-/

namespace Verify.MonthLength

open Time

@[simp] def monthLengthsOfDate (m : Nat × Nat) (dt : Date) :=
  m ∈ (monthLengths (isLeapYear dt.Year))
  ∧ m.fst = dt.Month.val ∧ dt.Day.val ≤ m.snd

def monthLengths_of_date (dt : Date) : {m // monthLengthsOfDate m dt} :=
  let a := List.findExisting
     (fun m => m.fst = dt.Month.val ∧ dt.Day.val ≤ m.snd)
    (Time.monthLengths (isLeapYear dt.Year))
    (by
      simp
      let ⟨m, hm⟩ := dt.IsValid
      have : (_, _) ∈ monthLengths (isLeapYear dt.Year) := hm.left
      exact ⟨m.1, by exact ⟨m.2, by simp_all⟩⟩)
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
  cases isleap <;> simp [monthLastDayAsDayOfYear', monthLengths]
  · omega
  · omega

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

private theorem monthLastDayAsDayOfYear'_month_1_day_1_not_lt (isleap : Bool)
    : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬a.1 = 1 → ¬a.2.1 ≤ 31 := by
  cases isleap <;> simp [monthLastDayAsDayOfYear']

theorem monthLastDayAsDayOfYear'_month_1_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.2.1 ≤ 31)
    : 1 = a.val.1 := by
  by_contra
  have := monthLastDayAsDayOfYear'_month_1_day_1_not_lt isleap a a.property.left (by omega)
  contradiction

theorem monthLastDayAsDayOfYear'_month_1_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : 31 ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 59 else 58))
    : a.val.1 = 1 := by
  by_contra
  have : ¬(31 ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 59 else 58)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(1 = a.fst)
      → ¬(31 ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 59 else 58)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : 31 ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 59 else 58) := by
    cases isleap <;> simp_all
  contradiction

theorem monthLastDayAsDayOfYear'_month_1_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 1)
  (h1 : 31 ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 59 else 58))
    : a.val.2.2 = 31 := by
  by_contra
  have : ¬(a.val.1 = 1 ∧ 31 ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 59 else 58)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(31 = a.snd.snd)
      → ¬(a.1 = 1 ∧ 31 ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 59 else 58)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 1 ∧ 31 ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 59 else 58) := by
    cases isleap <;> simp_all
  contradiction

private theorem monthLastDayAsDayOfYear'_month_1_day_1_not_eq (isleap : Bool)
    : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬a.2.1 = 1 → ¬a.1 = 1 := by
  cases isleap <;> simp [monthLastDayAsDayOfYear']

theorem monthLastDayAsDayOfYear'_day_of_month_1_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 1)
    : 1 = a.val.2.1 := by
  by_contra
  have := monthLastDayAsDayOfYear'_month_1_day_1_not_eq isleap a a.property.left (by omega)
  contradiction

theorem monthLastDayAsDayOfYear'_month_2_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : 1 < a.val.2.1 ) (h2 : a.val.2.1 ≤ 59)
    : 2 = a.val.1 := by
  by_contra
  have : ¬(1 < a.val.snd.fst ∧ a.val.snd.fst < 60) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬2 = a.1 → ¬(1 < a.2.1 ∧ a.2.1 < 60) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : 1 < a.val.2.1 ∧ a.val.2.1 < 60 := by omega
  contradiction

theorem monthLastDayAsDayOfYear'_day_of_month_2_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 2)
    : (if isleap then 32 else 32) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 2 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 32 else 32) = a.2.1 → ¬a.1 = 2 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction

theorem month_2_if_eq (isLeap : Bool) (h: ml ∈ monthLengths isLeap)
    : ml.1 = 2 → ml.2 = if isLeap then 29 else 28 := by
  intro
  rename_i h
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 2 → ml.2 = if isLeap then 29 else 28 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h)]

theorem monthLastDayAsDayOfYear'_month_3_eq' (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 30 else 29) < a.val.2.1)
  (h2 : a.val.2.1 ≤ (if isleap then 91 else 90))
    : 2 = a.val.1 ∨ 3 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 30 else 29) < a.val.snd.fst ∧ a.val.snd.fst ≤ (if isleap then 91 else 90)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(2 = a.fst ∨ 3 = a.fst)
      → ¬((if isleap then 30 else 29) < a.2.1 ∧ a.2.1 ≤ (if isleap then 91 else 90)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 30 else 29) < a.val.2.1 ∧ a.val.snd.fst ≤ (if isleap then 91 else 90) := by
    cases isleap <;> simp_all
  contradiction

theorem monthLastDayAsDayOfYear'_month_3_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 32 else 32) < a.val.2.1)
  (h2 : a.val.2.1 ≤ (if isleap then 91 else 90))
    : 3 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 32 else 32) < a.val.snd.fst ∧ a.val.snd.fst ≤ (if isleap then 91 else 90)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(3 = a.fst)
      → ¬((if isleap then 32 else 32) < a.2.1 ∧ a.2.1 ≤ (if isleap then 91 else 90)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 32 else 32) < a.val.2.1 ∧ a.val.snd.fst ≤ (if isleap then 91 else 90) := by
    cases isleap <;> simp_all
  contradiction

theorem monthLastDayAsDayOfYear'_day_of_month_3_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 3)
    : (if isleap then 61 else 60) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 3 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 61 else 60) = a.2.1 → ¬a.1 = 3 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_4_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 61 else 60) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 120 else 119))
    : 4 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 61 else 60) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 120 else 119)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬4 = a.1
        → ¬((if isleap then 61 else 60) < a.2.1 ∧ a.2.1 ≤ (if isleap then 120 else 119)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 61 else 60) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 120 else 119) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_4_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 4)
    : (if isleap then 92 else 91) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 4 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 92 else 91) = a.2.1 → ¬a.1 = 4 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_5_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 92 else 91) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 151 else 150))
    : 5 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 92 else 91) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 151 else 150)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬5 = a.1
        → ¬((if isleap then 92 else 91) < a.2.1 ∧ a.2.1 ≤ (if isleap then 151 else 150)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 92 else 91) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 151 else 150) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_5_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 5)
    : (if isleap then 122 else 121) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 5 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 122 else 121) = a.2.1 → ¬a.1 = 5 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq'`. -/
theorem monthLastDayAsDayOfYear'_month_5_eq' (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 91 else 90) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 151 else 150))
    : 4 = a.val.1 ∨ 5 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 91 else 90) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 151 else 150)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(4 = a.1 ∨ 5 = a.1)
        → ¬((if isleap then 91 else 90) < a.2.1 ∧ a.2.1 ≤ (if isleap then 151 else 150)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 91 else 90) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 151 else 150) := And.intro h1 h2
  contradiction

/-- Generated by `gen_month_if_eq`. -/
theorem month_4_if_eq (isLeap : Bool) (h: ml ∈ monthLengths isLeap)
    : ml.1 = 4 → ml.2 = 30 := by
  intro
  rename_i h
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 4 → ml.2 = 30 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h)]

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_6_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 122 else 121) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 181 else 180))
    : 6 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 122 else 121) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 181 else 180)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬6 = a.1
        → ¬((if isleap then 122 else 121) < a.2.1 ∧ a.2.1 ≤ (if isleap then 181 else 180)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 122 else 121) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 181 else 180) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_6_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 6)
    : (if isleap then 153 else 152) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 6 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 153 else 152) = a.2.1 → ¬a.1 = 6 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_7_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 153 else 152) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 212 else 211))
    : 7 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 153 else 152) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 212 else 211)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬7 = a.1
        → ¬((if isleap then 153 else 152) < a.2.1 ∧ a.2.1 ≤ (if isleap then 212 else 211)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 153 else 152) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 212 else 211) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_7_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 7)
    : (if isleap then 183 else 182) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 7 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 183 else 182) = a.2.1 → ¬a.1 = 7 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq'`. -/
theorem monthLastDayAsDayOfYear'_month_7_eq' (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 152 else 151) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 212 else 211))
    : 6 = a.val.1 ∨ 7 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 152 else 151) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 212 else 211)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(6 = a.1 ∨ 7 = a.1)
        → ¬((if isleap then 152 else 151) < a.2.1 ∧ a.2.1 ≤ (if isleap then 212 else 211)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 152 else 151) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 212 else 211) := And.intro h1 h2
  contradiction

/-- Generated by `gen_month_if_eq`. -/
theorem month_6_if_eq (isLeap : Bool) (h: ml ∈ monthLengths isLeap)
    : ml.1 = 6 → ml.2 = 30 := by
  intro
  rename_i h
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 6 → ml.2 = 30 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h)]

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_8_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 183 else 182) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 243 else 242))
    : 8 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 183 else 182) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 243 else 242)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬8 = a.1
        → ¬((if isleap then 183 else 182) < a.2.1 ∧ a.2.1 ≤ (if isleap then 243 else 242)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 183 else 182) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 243 else 242) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_8_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 8)
    : (if isleap then 214 else 213) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 8 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 214 else 213) = a.2.1 → ¬a.1 = 8 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_9_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 214 else 213) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 273 else 272))
    : 9 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 214 else 213) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 273 else 272)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬9 = a.1
        → ¬((if isleap then 214 else 213) < a.2.1 ∧ a.2.1 ≤ (if isleap then 273 else 272)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 214 else 213) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 273 else 272) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_9_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 9)
    : (if isleap then 245 else 244) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 9 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 245 else 244) = a.2.1 → ¬a.1 = 9 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction


/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_10_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 245 else 244) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 304 else 303))
    : 10 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 245 else 244) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 304 else 303)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬10 = a.1
        → ¬((if isleap then 245 else 244) < a.2.1 ∧ a.2.1 ≤ (if isleap then 304 else 303)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 245 else 244) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 304 else 303) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_10_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 10)
    : (if isleap then 275 else 274) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 10 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 275 else 274) = a.2.1 → ¬a.1 = 10 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq'`. -/
theorem monthLastDayAsDayOfYear'_month_10_eq' (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 244 else 243) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 304 else 303))
    : 9 = a.val.1 ∨ 10 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 244 else 243) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 304 else 303)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(9 = a.1 ∨ 10 = a.1)
        → ¬((if isleap then 244 else 243) < a.2.1 ∧ a.2.1 ≤ (if isleap then 304 else 303)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 244 else 243) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 304 else 303) := And.intro h1 h2
  contradiction

/-- Generated by `gen_month_if_eq`. -/
theorem month_9_if_eq (isLeap : Bool) (h: ml ∈ monthLengths isLeap)
    : ml.1 = 9 → ml.2 = 30 := by
  intro
  rename_i h
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 9 → ml.2 = 30 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h)]

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq`. -/
theorem monthLastDayAsDayOfYear'_month_11_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 275 else 274) < a.val.2.1 )
  (h2 : a.val.2.1 ≤ (if isleap then 334 else 333))
    : 11 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 275 else 274) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then 334 else 333)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬11 = a.1
        → ¬((if isleap then 275 else 274) < a.2.1 ∧ a.2.1 ≤ (if isleap then 334 else 333)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 275 else 274) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then 334 else 333) := And.intro h1 h2
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_day_of_month_eq`. -/
theorem monthLastDayAsDayOfYear'_day_of_month_11_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 11)
    : (if isleap then 306 else 305) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 11 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 306 else 305) = a.2.1 → ¬a.1 = 11 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction

theorem monthLastDayAsDayOfYear'_month_12_eq (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : (if isleap then 306 else 305) < a.val.2.1 )
    : 12 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 306 else 305) < a.val.snd.fst) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬12 = a.1
        → ¬((if isleap then 306 else 305) < a.2.1) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 306 else 305) < a.val.2.1 := h
  contradiction

theorem monthLastDayAsDayOfYear'_month_12_eq' (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : (if isleap then 305 else 304) < a.val.2.1 )
    : 11 = a.val.1 ∨ 12 = a.val.1 := by
  by_contra
  have : ¬((if isleap then 305 else 304) < a.val.snd.fst) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(11 = a.1 ∨ 12 = a.1)
        → ¬((if isleap then 305 else 304) < a.2.1) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 305 else 304) < a.val.2.1 := h
  contradiction

theorem monthLastDayAsDayOfYear'_day_of_month_12_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 12)
    : (if isleap then 336 else 335) = a.val.2.1 := by
  by_contra
  have : ¬a.val.1 = 12 := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then 336 else 335) = a.2.1 → ¬a.1 = 12 := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction

theorem month_11_if_eq (isLeap : Bool) (h: ml ∈ monthLengths isLeap)
    : ml.1 = 11 → ml.2 = 30 := by
  intro
  rename_i h
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 11 → ml.2 = 30 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h)]

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_2_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 60 else 59) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 90 else 89))
    : a.val.1 = 2 := by
  by_contra
  have : ¬((if isleap then 60 else 59) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 90 else 89)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(2 = a.fst)
     → ¬((if isleap then 60 else 59) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 90 else 89)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 60 else 59) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 90 else 89) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_2_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 2)
  (h1 : (if isleap then 60 else 59) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 90 else 89))
    : a.val.2.2 = if isleap then 60 else 59 := by
  by_contra
  have : ¬(a.val.1 = 2 ∧ (if isleap then 60 else 59) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 90 else 89)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 60 else 59)
      → ¬(a.1 = 2 ∧ (if isleap then 60 else 59) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 90 else 89)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 2 ∧ (if isleap then 60 else 59) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 90 else 89) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_3_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 91 else 90) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 120 else 119))
    : a.val.1 = 3 := by
  by_contra
  have : ¬((if isleap then 91 else 90) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 120 else 119)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(3 = a.fst)
     → ¬((if isleap then 91 else 90) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 120 else 119)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 91 else 90) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 120 else 119) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_3_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 3)
  (h1 : (if isleap then 91 else 90) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 120 else 119))
    : a.val.2.2 = if isleap then 91 else 90 := by
  by_contra
  have : ¬(a.val.1 = 3 ∧ (if isleap then 91 else 90) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 120 else 119)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 91 else 90)
      → ¬(a.1 = 3 ∧ (if isleap then 91 else 90) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 120 else 119)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 3 ∧ (if isleap then 91 else 90) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 120 else 119) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_4_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 121 else 120) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 151 else 150))
    : a.val.1 = 4 := by
  by_contra
  have : ¬((if isleap then 121 else 120) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 151 else 150)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(4 = a.fst)
     → ¬((if isleap then 121 else 120) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 151 else 150)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 121 else 120) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 151 else 150) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_4_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 4)
  (h1 : (if isleap then 121 else 120) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 151 else 150))
    : a.val.2.2 = if isleap then 121 else 120 := by
  by_contra
  have : ¬(a.val.1 = 4 ∧ (if isleap then 121 else 120) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 151 else 150)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 121 else 120)
      → ¬(a.1 = 4 ∧ (if isleap then 121 else 120) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 151 else 150)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 4 ∧ (if isleap then 121 else 120) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 151 else 150) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_5_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 152 else 151) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 181 else 180))
    : a.val.1 = 5 := by
  by_contra
  have : ¬((if isleap then 152 else 151) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 181 else 180)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(5 = a.fst)
     → ¬((if isleap then 152 else 151) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 181 else 180)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 152 else 151) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 181 else 180) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_5_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 5)
  (h1 : (if isleap then 152 else 151) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 181 else 180))
    : a.val.2.2 = if isleap then 152 else 151 := by
  by_contra
  have : ¬(a.val.1 = 5 ∧ (if isleap then 152 else 151) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 181 else 180)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 152 else 151)
      → ¬(a.1 = 5 ∧ (if isleap then 152 else 151) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 181 else 180)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 5 ∧ (if isleap then 152 else 151) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 181 else 180) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_6_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 182 else 181) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 212 else 211))
    : a.val.1 = 6 := by
  by_contra
  have : ¬((if isleap then 182 else 181) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 212 else 211)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(6 = a.fst)
     → ¬((if isleap then 182 else 181) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 212 else 211)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 182 else 181) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 212 else 211) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_6_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 6)
  (h1 : (if isleap then 182 else 181) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 212 else 211))
    : a.val.2.2 = if isleap then 182 else 181 := by
  by_contra
  have : ¬(a.val.1 = 6 ∧ (if isleap then 182 else 181) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 212 else 211)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 182 else 181)
      → ¬(a.1 = 6 ∧ (if isleap then 182 else 181) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 212 else 211)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 6 ∧ (if isleap then 182 else 181) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 212 else 211) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_7_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 213 else 212) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 243 else 242))
    : a.val.1 = 7 := by
  by_contra
  have : ¬((if isleap then 213 else 212) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 243 else 242)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(7 = a.fst)
     → ¬((if isleap then 213 else 212) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 243 else 242)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 213 else 212) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 243 else 242) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_7_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 7)
  (h1 : (if isleap then 213 else 212) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 243 else 242))
    : a.val.2.2 = if isleap then 213 else 212 := by
  by_contra
  have : ¬(a.val.1 = 7 ∧ (if isleap then 213 else 212) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 243 else 242)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 213 else 212)
      → ¬(a.1 = 7 ∧ (if isleap then 213 else 212) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 243 else 242)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 7 ∧ (if isleap then 213 else 212) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 243 else 242) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_8_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 244 else 243) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 273 else 272))
    : a.val.1 = 8 := by
  by_contra
  have : ¬((if isleap then 244 else 243) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 273 else 272)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(8 = a.fst)
     → ¬((if isleap then 244 else 243) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 273 else 272)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 244 else 243) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 273 else 272) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_8_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 8)
  (h1 : (if isleap then 244 else 243) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 273 else 272))
    : a.val.2.2 = if isleap then 244 else 243 := by
  by_contra
  have : ¬(a.val.1 = 8 ∧ (if isleap then 244 else 243) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 273 else 272)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 244 else 243)
      → ¬(a.1 = 8 ∧ (if isleap then 244 else 243) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 273 else 272)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 8 ∧ (if isleap then 244 else 243) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 273 else 272) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_9_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 274 else 273) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 304 else 303))
    : a.val.1 = 9 := by
  by_contra
  have : ¬((if isleap then 274 else 273) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 304 else 303)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(9 = a.fst)
     → ¬((if isleap then 274 else 273) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 304 else 303)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 274 else 273) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 304 else 303) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_9_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 9)
  (h1 : (if isleap then 274 else 273) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 304 else 303))
    : a.val.2.2 = if isleap then 274 else 273 := by
  by_contra
  have : ¬(a.val.1 = 9 ∧ (if isleap then 274 else 273) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 304 else 303)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 274 else 273)
      → ¬(a.1 = 9 ∧ (if isleap then 274 else 273) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 304 else 303)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 9 ∧ (if isleap then 274 else 273) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 304 else 303) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_10_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 305 else 304) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 334 else 333))
    : a.val.1 = 10 := by
  by_contra
  have : ¬((if isleap then 305 else 304) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 334 else 333)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(10 = a.fst)
     → ¬((if isleap then 305 else 304) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 334 else 333)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 305 else 304) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 334 else 333) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_10_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 10)
  (h1 : (if isleap then 305 else 304) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 334 else 333))
    : a.val.2.2 = if isleap then 305 else 304 := by
  by_contra
  have : ¬(a.val.1 = 10 ∧ (if isleap then 305 else 304) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 334 else 333)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 305 else 304)
      → ¬(a.1 = 10 ∧ (if isleap then 305 else 304) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 334 else 333)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 10 ∧ (if isleap then 305 else 304) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 334 else 333) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd_le`. -/
theorem monthLastDayAsDayOfYear'_month_11_eq_snd_le (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h1 : (if isleap then 335 else 334) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 365 else 364))
    : a.val.1 = 11 := by
  by_contra
  have : ¬((if isleap then 335 else 334) ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then 365 else 364)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(11 = a.fst)
     → ¬((if isleap then 335 else 334) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 365 else 364)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then 335 else 334) ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then 365 else 364) := by
    cases isleap <;> simp_all
  contradiction

/-- Generated by `gen_monthLastDayAsDayOfYear'_month_eq_snd`. -/
theorem monthLastDayAsDayOfYear'_month_11_eq_snd (dt : Date) (isleap : Bool)
    (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val })
  (h : a.val.1 = 11)
  (h1 : (if isleap then 335 else 334) ≤ a.val.2.2)
  (h2 : a.val.2.2 ≤ (if isleap then 365 else 364))
    : a.val.2.2 = if isleap then 335 else 334 := by
  by_contra
  have : ¬(a.val.1 = 11 ∧ (if isleap then 335 else 334) ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then 365 else 364)) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then 335 else 334)
      → ¬(a.1 = 11 ∧ (if isleap then 335 else 334) ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then 365 else 364)) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = 11 ∧ (if isleap then 335 else 334) ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then 365 else 364) := by
    cases isleap <;> simp_all
  contradiction
