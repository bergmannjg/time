import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.OrdinalDate
import Time.Verify.Calendar.MonthLength
import Time.Verify.Calendar.DayOfYear

/-!
## Theorems about `Time.findValidMonthDay` properties

Main theorems:

* `Verify.MonthDay.findValidMonthDay_month_eq`
* `Verify.MonthDay.findValidMonthDay_month_eq_incr`

-/

namespace Verify
namespace MonthDay

open Time
open Time.Notation
open MonthLength
open DayOfYear

theorem incr_of_yd_in (yd : Time.Icc 1 366) (isLeap : Bool)
  (hle : yd.val+1 ≤ if isLeap then 366 else 365)
     : 1 ≤ yd.val + 1 ∧ yd.val + 1 ≤ 366 := by
  simp [yd.property.left]
  cases isLeap <;> simp_all [hle]
  omega

theorem incr_of_day_in_intervall (dt : Date) (ml : { m // monthLengthsOfDate m dt })
  (h : dt.Day.val < ml.val.snd)
    : 1 ≤ dt.Day.val + 1 ∧ dt.Day.val + 1 ≤ 31 := by
  have : ml.val.snd ≤ 31 := by
    simp [monthLengths_days_in (isLeapYear dt.Year) ml.val ml.property.left]
  omega

/-- Day of year `yd` equals `(Time.monthLastDayAsDayOfYear' isLeap).val.snd.snd`
if `dt.Day.val = ml.val.snd` (if dt.Day is last day of month). -/
theorem yd_eq_monthLastDayAsDayOfYear'_val {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {a : { x // x ∈ monthLastDayAsDayOfYear' isLeap ∧ x.fst = dt.Month.val } }
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hmem : ml.val ∈ monthLengths (isLeapYear dt.Year) ∧ ml.val.fst = dt.Month.val ∧ dt.Day.val ≤ ml.val.snd)
  (heq : a.val.snd.fst + dt.Day.val - 1 = yd.val) (hl : isLeapYear dt.Year = isLeap)
    : a.val.snd.snd = yd.val := by
  have := a.property
  have := dt.Day.property
  simp [hl] at hmem
  have : a.val.snd.snd - a.val.snd.fst + 1 = dt.Day.val := by
    have := monthLastDayAsDayOfYear'_sub_of_monthLengths isLeap a.val ml.val
              a.property.left hmem.left (by simp_all)
    simp_all
  have hlt : a.val.2.1 < a.val.2.2 := monthLastDayAsDayOfYear'_days_sub_lt isLeap a a.property.left
  rw [← this] at heq
  have : a.val.snd.fst + (a.val.snd.snd - a.val.snd.fst + 1) - 1
        = a.val.snd.snd := by omega
  simp_all

namespace Notation

private def incr (n : Lean.TSyntax `num) (offset : Nat := 1) : Lean.TSyntax `num :=
  Lean.Quote.quote (n.getNat + offset)

private def decr (n : Lean.TSyntax `num) (offset : Nat := 1) : Lean.TSyntax `num :=
  Lean.Quote.quote (n.getNat - offset)

declare_syntax_cat ValidMonthDayMonthEq
syntax ident ws num ws num ws num ws num ws num ws num  ws num : ValidMonthDayMonthEq
syntax "validMonthDayMonthEq%" ValidMonthDayMonthEq : term

/-- proof of `... = dt.Month ∧ dt.Day.val + 1 = ...` if month `$m-1` has 31 days

* $m = (monthLastDayAsDayOfYear' true)[i].1
* $v = (monthLastDayAsDayOfYear' true)[i].2.1
* $v' = (monthLastDayAsDayOfYear' false)[i].2.1
* $p = (monthLastDayAsDayOfYear' true)[i-1].2.1
* $p' = (monthLastDayAsDayOfYear' false)[i-1].2.1
* $n = (monthLastDayAsDayOfYear' true)[i].2.2
* $n' = (monthLastDayAsDayOfYear' false)[i].2.2

-/
macro_rules
| `(validMonthDayMonthEq% $t:ident $m:num $v:num $v':num $p:num $p':num $n:num $n':num) =>
    `((fun {dt} isLeap yd {ml} hml h heq hle hl hne hyd  => by
  let dy'MonthEq := dy'MonthEq% $m:num $(decr v) $(decr v') $p $p' $(decr n) $(decr n')
  let dy'MonthDayEq := dy'MonthDayEq% $m:num $(decr v) $(decr v') $p $p' $(decr n) $(decr n') $v $v'
  unfold $t
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'MonthEq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'MonthDayEq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'MonthEq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'MonthDayEq dt false (by omega) hne hyd
    simp_all
    : ∀ {dt : Date} (isLeap : Bool) (yd : Icc 1 366) {ml : { m // monthLengthsOfDate m dt }},
        ml = monthLengths_of_date dt →
        ∀ (h : dt.Day.val < ml.val.snd),
        dy' isLeap dt.Month dt.Day = yd.val →
        ∀ (hle : yd.val + 1 ≤ if isLeap = true then 366 else 365)
          (hl : isLeapYear dt.Year = isLeap)
          (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[($m-2)].snd)
          (hyd : yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨($m-1), by simp⟩).snd),
          ($t dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩
              hl hne hyd).Month = dt.Month
          ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
            = ($t dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day))

--#check validMonthDayMonthEq% findValidMonthDay_4 4 92 91 61 60 121 120

declare_syntax_cat ValidMonthDayMonthEq'
syntax ident ws num ws num ws num ws num ws num ws num ws num : ValidMonthDayMonthEq'
syntax "validMonthDayMonthEq'%" ValidMonthDayMonthEq' : term

/-- proof of `... = dt.Month ∧ dt.Day.val + 1 = ...` if month `$m-1` has less than 31 days

* $m = (monthLastDayAsDayOfYear' true)[i].1
* $v = (monthLastDayAsDayOfYear' true)[i].2.1
* $v' = (monthLastDayAsDayOfYear' false)[i].2.1
* $p = (monthLastDayAsDayOfYear' true)[i-1].2.1
* $p' = (monthLastDayAsDayOfYear' false)[i-1].2.1
* $n = (monthLastDayAsDayOfYear' true)[i].2.2
* $n' = (monthLastDayAsDayOfYear' false)[i].2.2

-/
macro_rules
| `(validMonthDayMonthEq'% $t:ident $m:num $v:num $v':num $p:num $p':num $n:num $n':num) =>
    `((fun {dt} isLeap yd {ml} hml h heq hle hl hne hyd  => by
  let dy'MonthEq := dy'MonthEq'% $m:num $(decr v) $(decr v') $p $p' $(decr n) $(decr n')
                        $n $n' $(decr m)
  let dy'MonthDayEq := dy'MonthDayEq'% $m:num $(decr v) $(decr v') $p $p' $(decr n) $(decr n')
                          $n $n' $(decr v 2) $(decr v' 2) $v $(decr m)
  unfold $t
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (monthIfLt% $(decr m):num) true hml (by simp_all) hl
    simp [dy'MonthEq dt true (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'MonthDayEq dt true (by omega) this hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (monthIfLt% $(decr m):num) false hml (by simp_all) hl
    simp [dy'MonthEq dt false (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'MonthDayEq dt false (by omega) this hne hyd
    simp_all    : ∀ {dt : Date} (isLeap : Bool) (yd : Icc 1 366) {ml : { m // monthLengthsOfDate m dt }},
        ml = monthLengths_of_date dt →
        ∀ (h : dt.Day.val < ml.val.snd),
        dy' isLeap dt.Month dt.Day = yd.val →
        ∀ (hle : yd.val + 1 ≤ if isLeap = true then 366 else 365)
          (hl : isLeapYear dt.Year = isLeap)
          (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[($m-2)].snd)
          (hyd : yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨($m-1), by simp⟩).snd),
          ($t dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩
              hl hne hyd).Month = dt.Month
          ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
            = ($t dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day))

--#check validMonthDayMonthEq'% findValidMonthDay_5 5 122 121 92 91 152 151

--#check validMonthDayMonthEq'% findValidMonthDay_3 3 61 60 32 32 91 90

declare_syntax_cat ValidMonthDayMonthEqIncr'
syntax num ws num ws num ws num ws num : ValidMonthDayMonthEqIncr'
syntax "ValidMonthDayMonthEqIncr'%" ValidMonthDayMonthEqIncr' : term

/-- proof of `dt.Month.val = $m ∧ yd.val = (if isLeap then $v else $v')`

* $m = (monthLastDayAsDayOfYear' true)[i-1].1
* $v = (monthLastDayAsDayOfYear' true)[i-1].2.2
* $v' = (monthLastDayAsDayOfYear' false)[i-1].2.2
* $p = (monthLastDayAsDayOfYear' true)[i].2.2
* $p' = (monthLastDayAsDayOfYear' false)[i].2.2

-/
macro_rules
| `(ValidMonthDayMonthEqIncr'% $m:num $v:num $v':num $p:num $p':num) =>
    `((fun {dt} isLeap yd {ml} hml h heq hl h1 h2  => by
  simp [dy'] at heq
  generalize memOfMonth isLeap dt.Month = a at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := (monthLastDayEqSndLe% $m:num $v $v' $p $p')  dt isLeap a h1 h2
  have := (monthLastDayEqSnd% $m:num $v $v' $(decr p) $(decr p')) dt isLeap a this h1 h2
  simp_all
    : ∀ {dt : Date} (isLeap : Bool) (yd : Icc 1 366) {ml : { m // monthLengthsOfDate m dt }},
        ml = monthLengths_of_date dt →
        dt.Day.val = ml.val.snd →
        dy' isLeap dt.Month dt.Day = yd.val →
        isLeapYear dt.Year = isLeap →
        (if isLeap = true then $v else $v') ≤ yd.val →
        (yd.val ≤ if isLeap = true then $(decr p) else $(decr p')) →
        dt.Month.val = $m ∧ yd.val = if isLeap = true then $v else $v'))

--#check ValidMonthDayMonthEqIncr'% 2 60 59 91 90

declare_syntax_cat ValidMonthDayMonthEqIncr
syntax ident ws num ws num ws num ws num ws num : ValidMonthDayMonthEqIncr
syntax "ValidMonthDayMonthEqIncr%" ValidMonthDayMonthEqIncr : term

/-- proof of `($t ...).Month.val = dt.Month.val + 1 ∧ ($t ...).Day.val = 1`

* $m = (monthLastDayAsDayOfYear' true)[i-1].1
* $v = (monthLastDayAsDayOfYear' true)[i-1].2.2
* $v' = (monthLastDayAsDayOfYear' false)[i-1].2.2
* $p = (monthLastDayAsDayOfYear' true)[i].2.2
* $p' = (monthLastDayAsDayOfYear' false)[i].2.2

-/
macro_rules
| `(validMonthDayMonthEqIncr% $t:ident $m:num $v:num $v':num $p:num $p':num) =>
    `((fun {dt} isLeap yd {ml} hml h hm heq hl hn hyd => by
  unfold $t
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  split at hyd
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [(ValidMonthDayMonthEqIncr'% $m:num $v $v' $p $p') true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [(ValidMonthDayMonthEqIncr'% $m:num $v $v' $p $p') false yd hml h heq hl (by simp_all; omega) (by simp_all)]
    : ∀ {dt : Date} (isLeap : Bool) (yd : Icc 1 366) {ml : { m // monthLengthsOfDate m dt }},
        ml = monthLengths_of_date dt →
        dt.Day.val = ml.val.snd →
        ∀ (hm : dt.Month.val < 12)
          (heq : dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
          (hn : ¬yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨$m-1, by simp⟩).snd)
          (hyd : yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨$m, by simp⟩).snd),
          ($t dt.Year isLeap ⟨yd.val + 1,
            by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩ hl hn hyd).Month
          = ⟨dt.Month.val + 1, by omega⟩ ∧
          ($t dt.Year isLeap ⟨yd.val + 1,
            by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩ hl hn hyd).Day
          = ⟨1, by omega⟩))

--#check validMonthDayMonthEqIncr% findValidMonthDay_3 2 60 59 91 90

end Notation

theorem incr_of_day_is_valid (dt : Date) (ml : { m // monthLengthsOfDate m dt })
  (h : dt.Day.val < ml.val.snd)
    : ∃ m, m ∈ monthLengths (isLeapYear dt.Year)
            ∧ m.fst = dt.Month.val
            ∧ (⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩ : Icc 1 31).val ≤ m.snd := by
  simp [monthLengthsOfDate] at ml
  exact ⟨ml.val, by simp_all [ml.property, Nat.le_of_lt_add_one]⟩

theorem incr_of_month_is_valid (dt : Date) (h : dt.Month.1 < 12)
  : ∃ a ∈ (monthLengths (isLeapYear dt.Year)),
      a.1 = (⟨dt.Month.1 + 1, by simp [dt.Month.property.left, (Nat.add_one_le_of_lt h)]⟩
              : Icc 1 12).val
      ∧ (⟨1, by simp⟩ : Icc 1 31).val ≤ a.2 := by
  cases (isLeapYear dt.Year) <;> simp_all [monthLengths] <;> omega

theorem OrdinalDate_of_common_no_leapYear (dt : OrdinalDate) (v : Icc 1 365)
  (h : dt.dayOfYear = .common v) : isLeapYear dt.year = false := by
  have := dt.isValid
  simp_all

theorem not_leapYear_eq (year : Int) (h : isLeapYear year = false) (h2 : year % 4 = 0)
    : ¬(year % 400 = 0 ∨ ¬year % 100 = 0) := by
  simp [isLeapYear] at h
  have := h h2
  simp [this]

theorem dateToOrdinalDate_year_eq (dt : Date) : (dateToOrdinalDate dt).year = dt.Year := by
  simp [dateToOrdinalDate]
  split <;> simp_all

def date_of_dy' {dt : Date} : OrdinalDate :=
  ⟨ dt.Year,
    if isLeapYear dt.Year
    then .leap ⟨Time.dy' true dt.Month dt.Day, by
      simp [le_dy']
      exact dy'_le true dt.Month dt.Day⟩
    else .common ⟨Time.dy' false dt.Month dt.Day, by
      simp [le_dy']
      exact dy'_le false dt.Month dt.Day⟩,
  (by
    split
    · rename_i heq'
      split at heq'
      · contradiction
      · simp_all
    · rename_i heq'
      split at heq'
      · simp_all
      · contradiction)⟩

def dateToOrdinalDate' (dt : Date) : OrdinalDate :=
  ⟨ dt.Year,
         if isLeapYear dt.Year
         then .leap ⟨Time.dy' true dt.Month dt.Day, by
            simp [le_dy']
            exact dy'_le true dt.Month dt.Day⟩
         else .common ⟨Time.dy' false dt.Month dt.Day, by
            simp [le_dy']
            exact dy'_le false dt.Month dt.Day⟩,
        (by
          split
          · rename_i heq'
            split at heq'
            · contradiction
            · simp_all
          · rename_i heq'
            split at heq'
            · simp_all
            · contradiction)⟩

theorem dateToOrdinalDate'_year_eq (dt : Date) : (dateToOrdinalDate' dt).year = dt.Year := by
  simp [dateToOrdinalDate']

theorem dateToOrdinalDate'_dateToOrdinalDate_eq {dt : Date}
    : dateToOrdinalDate' dt = dateToOrdinalDate dt := by
  simp [dateToOrdinalDate', dateToOrdinalDate]
  split <;> simp [Icc, Subtype.ext_iff] <;> rw [dy_eq_dy']

theorem next_date_of_day_lt_top (dt : Date)
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd ∨ dt.Month.val < 12)
    : OrdinalDate.DayOfYear.lt_top (dateToOrdinalDate' dt).dayOfYear := by
  rw [dateToOrdinalDate'_dateToOrdinalDate_eq]
  simp [OrdinalDate.DayOfYear.lt_top]
  have := dy_lt_of_day_or_month_lt h
  split<;> simp_all

theorem next_date_of_day_lt_eq_incr' {dt : Date} {dt' : OrdinalDate}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd ∨ dt.Month.val < 12)
  (heq : dt' = dateToOrdinalDate dt)
    : OrdinalDate.DayOfYear.incr (dateToOrdinalDate' dt) (next_date_of_day_lt_top dt h)
    = OrdinalDate.next_date dt' := by
  unfold OrdinalDate.next_date OrdinalDate.DayOfYear.incr
  split <;> simp_all
  · rename_i dy _ h_dt_dayOfYear_common
    have hlt := dy_lt_of_day_or_month_lt h
    rw [← dateToOrdinalDate'_dateToOrdinalDate_eq] at heq
    split <;> try simp_all
    · rename_i heq' _ dy' _ h_dt'_dayOfYear_common
      rw [← heq'] at h_dt_dayOfYear_common
      have : dy = dy' := by
        rw [h_dt_dayOfYear_common] at h_dt'_dayOfYear_common
        simp [Subtype] at h_dt'_dayOfYear_common
        exact  Subtype.ext_iff.mp h_dt'_dayOfYear_common
      split <;> simp_all
    · rename_i heq' _ _ _ h_dt'_dayOfYear_leap
      rw [← heq', h_dt'_dayOfYear_leap] at h_dt_dayOfYear_common
      contradiction
  · rename_i dy _ h_dt_dayOfYear_leap
    have hlt := dy_lt_of_day_or_month_lt h
    rw [← dateToOrdinalDate'_dateToOrdinalDate_eq] at heq
    split <;> try simp_all
    · rename_i heq' _ dy' _ h_dt'_dayOfYear_common
      rw [heq', h_dt_dayOfYear_leap] at h_dt'_dayOfYear_common
      contradiction
    · rename_i heq' _ dy' _ h_dt'_dayOfYear_leap
      rw [← heq'] at h_dt_dayOfYear_leap
      have : dy = dy' := by
        rw [h_dt_dayOfYear_leap] at h_dt'_dayOfYear_leap
        simp [Subtype] at h_dt'_dayOfYear_leap
        exact  Subtype.ext_iff.mp h_dt'_dayOfYear_leap
      split <;> simp_all

theorem findValidMonthDay_year_eq (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap) (hle : yd.val ≤ if isLeap then 366 else 365)
    : (findValidMonthDay year isLeap yd hl hle).Year = year := by
  unfold findValidMonthDay
  split <;> try simp [findValidMonthDay_1]
  split <;> try simp [findValidMonthDay_2]
  split <;> try simp [findValidMonthDay_3]
  split <;> try simp [findValidMonthDay_4]
  split <;> try simp [findValidMonthDay_5]
  split <;> try simp [findValidMonthDay_6]
  unfold findValidMonthDay_tail
  split <;> try simp [findValidMonthDay_7]
  split <;> try simp [findValidMonthDay_8]
  split <;> try simp [findValidMonthDay_9]
  split <;> try simp [findValidMonthDay_10]
  split <;> try simp [findValidMonthDay_11]
  simp [findValidMonthDay_12]

theorem findValidMonthDay_1_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }} (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨0, by simp⟩).2)
    : (findValidMonthDay_1 year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_1 year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hyd).Day
           := by
  simp [findValidMonthDay_1]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  split at hyd <;> simp_all
  · simp [dy'_month_1_eq dt true (by rw [heq]; omega)]
    have := dy'_month_1_day_eq dt true (by
      rw [← heq] at hyd
      exact hyd)
    simp_all
  · have := dy'_month_1_eq dt false (by rw [heq]; omega)
    have := dy'_month_1_day_eq dt false (by
      rw [← heq] at hyd
      exact hyd)
    simp_all

theorem findValidMonthDay_12_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[10].snd)
    : (findValidMonthDay_12 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne
              (by have := dy'_add_one_hle h; simp_all)).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_12 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne
              (by have := dy'_add_one_hle h; simp_all)).Day
           := by
  simp [findValidMonthDay_12]
  simp [Icc, Subtype.ext_iff]
  have := incr_of_day_in_intervall dt ml h
  cases isLeap <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    have := (month_11_if_lt false hml (by simp_all) hl)
    simp [dy'_month_12_eq dt false (by omega) this hne]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_12_day_eq dt false (by omega) this hne
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    have := (month_11_if_lt true hml (by simp_all) hl)
    simp [dy'_month_12_eq dt true (by omega) this hne]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_12_day_eq dt true (by omega) this hne
    simp_all

set_option maxHeartbeats 2000000 in
/-- For a day of year `yd`, if `dt.Day` is not last day of month, then

* (Time.findValidMonthDay dt.Year (yd + 1)).Month = dt.Month
* (Time.findValidMonthDay dt.Year (yd + 1)).Day = dt.Day + 1

-/
theorem findValidMonthDay_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
    : (findValidMonthDay dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hle).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hle).Day := by
  unfold findValidMonthDay
  split
  · rename_i hyd
    exact findValidMonthDay_1_month_eq isLeap yd h heq hle hyd
  · split
    . rename_i hne hyd
      exact (validMonthDayMonthEq% findValidMonthDay_2 2 32 32 1 1 60 59) isLeap yd hml h heq hle hl hne hyd
    · split
      · rename_i hne' hne hyd
        exact (validMonthDayMonthEq'% findValidMonthDay_3 3 61 60 32 32 91 90) isLeap yd hml h heq hle hl hne hyd
      · split
        · rename_i hne hyd
          exact ((validMonthDayMonthEq% findValidMonthDay_4 4 92 91 61 60 121 120)) isLeap yd hml h heq hle hl hne hyd
        · split
          · rename_i hne hyd
            exact (validMonthDayMonthEq'% findValidMonthDay_5 5 122 121 92 91 152 151) isLeap yd hml h heq hle hl hne hyd
          · split
            · rename_i hne hyd
              exact (validMonthDayMonthEq% findValidMonthDay_6 6 153 152 122 121 182 181) isLeap yd hml h heq hle hl hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact (validMonthDayMonthEq'% findValidMonthDay_7 7 183 182 153 152 213 212) isLeap yd hml h heq hle hl hne hyd
              · split
                · rename_i hne hyd
                  exact (validMonthDayMonthEq% findValidMonthDay_8 8 214 213 183 182 244 243) isLeap yd hml h heq hle hl hne hyd
                · split
                  · rename_i hne hyd
                    exact (validMonthDayMonthEq% findValidMonthDay_9 9 245 244 214 213 274 273) isLeap yd hml h heq hle hl hne hyd
                  · split
                    · rename_i hne hyd
                      exact (validMonthDayMonthEq'% findValidMonthDay_10 10 275 274 245 244 305 304) isLeap yd hml h heq hle hl hne hyd
                    · split
                      · rename_i hne hyd
                        exact (validMonthDayMonthEq% findValidMonthDay_11 11 306 305 275 274 335 334) isLeap yd hml h heq hle hl hne hyd
                      · rename_i hne
                        exact findValidMonthDay_12_month_eq isLeap yd hml h heq hle hl hne

theorem monthLengths_month_1_eq_31_ne (isleap : Bool)
    : ∀ a ∈ monthLengths isleap, ¬31 = a.2 → ¬a.1 = 1 := by
  cases isleap <;> simp [monthLengths]

theorem monthLengths_month_1_eq_31 (isleap : Bool)
  (a : { x // x ∈ monthLengths isleap}) (h : a.val.1 = 1)
    : a.val.2 = 31 := by
  by_contra
  have := monthLengths_month_1_eq_31_ne isleap a a.property (by omega)
  contradiction

theorem findValidMonthDay_1_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨0, by simp⟩).2)
    : (findValidMonthDay_1 dt.Year isLeap ⟨yd + 1,
          by cases isLeap <;> simp_arith [monthLastDayAsDayOfYear] at hyd <;> omega⟩
          hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_1 dt.Year isLeap ⟨yd + 1,
          by cases isLeap <;> simp_arith [monthLastDayAsDayOfYear] at hyd <;> omega⟩
          hyd).Day = ⟨1, by omega⟩  := by
  simp [monthLastDayAsDayOfYear] at hyd
  have : yd.val ≤ 30 := by split at hyd <;> simp_all
  have : ¬yd.val ≤ 30 := by
    have h := dy'_month_1_eq dt isLeap (by rw [heq]; omega)
    have := monthLengths_month_1_eq_31 isLeap
          ⟨ml.val, by have := ml.property.left; simp_all [hl]⟩
          (by have := ml.property.right.left; simp [← h] at this; simp_all)
    have := dy'_month_1_day_eq dt isLeap (by rw [heq]; omega)
    simp_all
  contradiction

theorem findValidMonthDay_12_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 335 else 334) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap = true then 365 else 364)
    : dt.Month.val = 11 ∧ yd.val = (if isLeap then 335 else 334) := by
  simp [dy'] at heq
  generalize memOfMonth isLeap dt.Month = a at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_sub_le_31 isLeap a a.property.left
  have := (monthLastDayEqSndLe% 11 335 334 366 365) dt isLeap a h1 (by simp; omega)
  have := (monthLastDayEqSnd% 11 335 334 366 365) dt isLeap a this h1
              (by cases isLeap <;> simp <;> simp [] at h2 <;> omega)
  simp_all

theorem findValidMonthDay_12_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨10, by simp⟩).2)
  (hle : yd.val + 1 ≤ if isLeap = true then 366 else 365)
    : (findValidMonthDay_12 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all; omega⟩
          hl hn (by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega)).Month
        = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_12 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all; omega⟩
          hl hn (by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega)).Day
        = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_12]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear]
  split
  · simp []
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · simp [] at hn
      simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_12_month_eq_incr' true yd hml h heq hl
                (by simp_all; omega) hle]
    · contradiction
  · simp []
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_12_month_eq_incr' false yd hml h heq hl
                (by simp_all; omega) hle]

theorem yd_add_one_lt {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap) (hle : yd.val+1 ≤ if isLeap then 366 else 365)
    : 1 ≤ yd.val + 1 ∧ yd.val + 1 ≤ 366 := by
  simp [hle]
  have := @dy'_lt_of_month_lt dt hm
  simp [heq, hl] at this
  cases isLeap <;> simp_all
  omega

set_option maxHeartbeats 2000000 in
/-- For a day of year `yd`, if `dt.Day` is equal to last day of month, then

* (Time.findValidMonthDay dt.Year (yd + 1)).Month = dt.Month + 1
* (Time.findValidMonthDay dt.Year (yd + 1)).Day = 1

-/
theorem findValidMonthDay_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap) (hle : yd.val+1 ≤ if isLeap then 366 else 365)
    : (findValidMonthDay dt.Year isLeap ⟨yd+1, yd_add_one_lt isLeap yd hm heq hl hle⟩
        hl hle).Month
    = ⟨dt.Month.val + 1, by omega⟩
    ∧ (findValidMonthDay dt.Year isLeap ⟨yd+1, yd_add_one_lt isLeap yd hm heq hl
          hle⟩ hl hle).Day
    = ⟨1, by simp⟩ := by
  unfold findValidMonthDay
  split
  · rename_i hyd
    exact findValidMonthDay_1_month_eq_incr isLeap yd hml h hm heq hl hyd
  · split
    · rename_i hne hyd
      exact (validMonthDayMonthEqIncr% findValidMonthDay_2 1 31 31 60 59) isLeap yd hml h hm heq hl hne hyd
    · split
      · rename_i hne hyd
        exact (validMonthDayMonthEqIncr% findValidMonthDay_3 2 60 59 91 90) isLeap yd hml h hm heq hl hne hyd
      · split
        · rename_i hne hyd
          exact (validMonthDayMonthEqIncr% findValidMonthDay_4 3 91 90 121 120) isLeap yd hml h hm heq hl hne hyd
        · split
          · rename_i hne hyd
            exact (validMonthDayMonthEqIncr% findValidMonthDay_5 4 121 120 152 151) isLeap yd hml h hm heq hl hne hyd
          · split
            · rename_i hne hyd
              exact (validMonthDayMonthEqIncr% findValidMonthDay_6 5 152 151 182 181) isLeap yd hml h hm heq hl hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact (validMonthDayMonthEqIncr% findValidMonthDay_7 6 182 181 213 212) isLeap yd hml h hm heq hl hne hyd
              · split
                · rename_i hne hyd
                  exact (validMonthDayMonthEqIncr% findValidMonthDay_8 7 213 212 244 243) isLeap yd hml h hm heq hl hne hyd
                · split
                  · rename_i hne hyd
                    exact (validMonthDayMonthEqIncr% findValidMonthDay_9 8 244 243 274 273) isLeap yd hml h hm heq hl hne hyd
                  · split
                    · rename_i hne hyd
                      exact (validMonthDayMonthEqIncr% findValidMonthDay_10 9 274 273 305 304) isLeap yd hml h hm heq hl hne hyd
                    · split
                      · rename_i hne hyd
                        exact (validMonthDayMonthEqIncr% findValidMonthDay_11 10 305 304 335 334) isLeap yd hml h hm heq hl hne hyd
                      · rename_i hne
                        exact findValidMonthDay_12_month_eq_incr isLeap yd hml h hm heq hl hne hle
