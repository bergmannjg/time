import Time
import Time.Data.List.Basic

/-!
## Theorems about `Time.monthLengths` properties
-/

namespace Verify.MonthLength

open Time

namespace Notation

declare_syntax_cat monthLastDayMonthEq
syntax num ws num ws num ws num ws num : monthLastDayMonthEq
syntax "monthLastDayMonthEq%" monthLastDayMonthEq : term

/-- proof of `$m = a.val.fst` -/
macro_rules
| `(monthLastDayMonthEq% $m:num $p:num $p':num $n:num $n':num) =>
    `((fun dt isleap a h1 h2 => by
  by_contra
  have : ¬((if isleap then $p else $p') < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then $n else $n')) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬$m = a.1
        → ¬((if isleap then $p else $p') < a.2.1 ∧ a.2.1 ≤ (if isleap then $n else $n')) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then $p else $p') < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then $n else $n') := And.intro h1 h2
  contradiction
    : ∀ (dt : Date) (isleap : Bool)
        (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }),
        (if isleap = true then $p else $p') < a.val.snd.fst →
        (a.val.snd.fst ≤ if isleap = true then $n else $n') →
        $m = a.val.fst))

--#check monthLastDayMonthEq% 4 61 60 120 119

declare_syntax_cat monthLastDayMonthEq'
syntax num ws num ws num ws num ws num : monthLastDayMonthEq'
syntax "monthLastDayMonthEq'%" monthLastDayMonthEq' : term

/-- proof of `($m-1) = a.val.fst ∨ $m = a.val.fst` -/
macro_rules
| `(monthLastDayMonthEq'% $m:num $v:num $v':num $p:num $p':num) =>
    `((fun dt isleap a h1 h2 => by
  by_contra
  have : ¬((if isleap then ($p-1) else ($p'-1)) < a.val.snd.fst
           ∧ a.val.snd.fst ≤ (if isleap then ($v-1) else ($v'-1))) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(($m-1) = a.1 ∨ $m = a.1)
        → ¬((if isleap then ($p-1) else ($p'-1)) < a.2.1 ∧ a.2.1 ≤ (if isleap then ($v-1) else ($v'-1))) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then ($p-1) else ($p'-1)) < a.val.2.1
         ∧ a.val.2.1 ≤ (if isleap then ($v-1) else ($v'-1)) := And.intro h1 h2
  contradiction
    : ∀ (dt : Date) (isleap : Bool)
        (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }),
        (if isleap = true then ($p-1) else ($p'-1)) < a.val.snd.fst →
        (a.val.snd.fst ≤ if isleap = true then ($v-1) else ($v'-1)) →
        ($m-1) = a.val.fst ∨ $m = a.val.fst))

--#check monthLastDayMonthEq'% 5 121 120 92 91

declare_syntax_cat monthLastDayMonthDayEq
syntax num ws num ws num : monthLastDayMonthDayEq
syntax "monthLastDayMonthDayEq%" monthLastDayMonthDayEq : term

/-- proof of `(if isleap = true then $v else $v') = a.val.snd.fst` -/
macro_rules
| `(monthLastDayMonthDayEq% $m:num $v:num $v':num) =>
    `((fun dt isleap a h => by
  by_contra
  have : ¬a.val.1 = $m := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(if isleap then $v else $v') = a.2.1 → ¬a.1 = $m := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  contradiction
    : ∀ (dt : Date) (isleap : Bool)
        (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }),
        a.val.fst = $m →
        (if isleap = true then $v else $v') = a.val.snd.fst))

--#check monthLastDayMonthDayEq% 5 122 121

declare_syntax_cat monthIfEq
syntax num : monthIfEq
syntax "monthIfEq%" monthIfEq : term

/-- proof of `ml.snd = 30` -/
macro_rules
| `(monthIfEq% 2) =>
    `((fun {ml} isLeap h h' => by
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = 2 → ml.2 = if isLeap then 29 else 28 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h')]
    : ∀ {ml : Nat × Nat} (isLeap : Bool), ml ∈ monthLengths isLeap
        → ml.fst = 2
        → ml.snd = if isLeap then 29 else 28))
| `(monthIfEq% $m:num) =>
    `((fun {ml} isLeap h h' => by
  have : ∀ ml, ml ∈ monthLengths isLeap ∧ ml.1 = $m → ml.2 = 30 := by
    simp [monthLengths]
  simp [this ml (And.intro (by simp_all) h')]
    : ∀ {ml : Nat × Nat} (isLeap : Bool), ml ∈ monthLengths isLeap
        → ml.fst = $m
        → ml.snd = 30))

declare_syntax_cat monthLastDayEqSndLe
syntax num ws num ws num ws num ws num: monthLastDayEqSndLe
syntax "monthLastDayEqSndLe%" monthLastDayEqSndLe : term

/-- proof of `a.val.fst = $m` -/
macro_rules
| `(monthLastDayEqSndLe% $m:num $v:num $v':num $n:num $n':num) =>
    `((fun dt isleap a h1 h2 => by
  by_contra
  have : ¬((if isleap then $v else $v') ≤ a.val.snd.snd ∧ a.val.snd.snd ≤ (if isleap then ($n-1) else ($n'-1))) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬($m = a.fst)
     → ¬((if isleap then $v else $v') ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then ($n-1) else ($n'-1))) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : (if isleap then $v else $v') ≤ a.val.2.2 ∧ a.val.snd.snd ≤ (if isleap then ($n-1) else ($n'-1)) := by
    cases isleap <;> simp_all
  contradiction
    : ∀ (dt : Date) (isleap : Bool)
        (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }),
        (if isleap = true then $v else $v') ≤ a.val.snd.snd →
        (a.val.snd.snd ≤ if isleap = true then ($n-1) else ($n'-1)) →
        a.val.fst = $m))

--#check monthLastDayEqSndLe% 3 91 90 121 120

declare_syntax_cat monthLastDayEqSnd
syntax num ws num ws num ws num ws num: monthLastDayEqSnd
syntax "monthLastDayEqSnd%" monthLastDayEqSnd : term

/-- proof of `a.val.snd.snd = if isleap = true then $v else $v'` -/
macro_rules
| `(monthLastDayEqSnd% $m:num $v:num $v':num $n:num $n':num) =>
    `((fun dt isleap a h1 h2 => by
  by_contra
  have : ¬(a.val.1 = $m ∧ (if isleap then $v else $v') ≤ a.val.snd.snd
           ∧ a.val.snd.snd ≤ (if isleap then $n else $n')) := by
    have : ∀ a ∈ monthLastDayAsDayOfYear' isleap, ¬(a.2.2 = if isleap then $v else $v')
      → ¬(a.1 = $m ∧ (if isleap then $v else $v') ≤ a.2.2 ∧ a.2.2 ≤ (if isleap then $n else $n')) := by
      cases isleap <;> simp [monthLastDayAsDayOfYear']
    exact this a a.property.left (by omega)
  have : a.val.1 = $m ∧ (if isleap then $v else $v') ≤ a.val.2.2
         ∧ a.val.snd.snd ≤ (if isleap then $n else $n') := by
    cases isleap <;> simp_all
  contradiction
    : ∀ (dt : Date) (isleap : Bool)
        (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }),
        a.val.fst = $m →
        (if isleap = true then $v else $v') ≤ a.val.snd.snd →
        (a.val.snd.snd ≤ if isleap = true then $n else $n') →
        a.val.snd.snd = if isleap = true then $v else $v'))

--#check monthLastDayEqSnd% 3 91 90 120 119

end Notation

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
  exact (monthLastDayMonthEq% 1 0 0 31 31) dt isleap a
          (by simp [monthLastDayAsDayOfYear'_snd_fst_lt isleap a.val a.property.left])
          (by simp [h])

theorem monthLastDayAsDayOfYear'_day_of_month_1_eq (dt : Date) (isleap : Bool)
  (a : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = dt.Month.val }) (h : a.val.1 = 1)
    : 1 = a.val.2.1 := by
  have := ( monthLastDayMonthDayEq% 1 1 1) dt isleap a h
  simp_all

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
