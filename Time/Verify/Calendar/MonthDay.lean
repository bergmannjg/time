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
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  unfold findValidMonthDay_tail
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]
  split <;> try simp [findValidMonthDay_n]

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

theorem findValidMonthDay_n_month_eq {dt : Date} (isLeap : Bool) (i : Nat) (yd : Time.Icc 1 366)
  (hle' : 1 ≤ i)
  (hlt : i < (monthLengths isLeap).length)
  (hlt' : i < (monthLastDayAsDayOfYear isLeap).length)
  (hl : isLeapYear dt.Year = isLeap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hydn : ¬yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨i-1, by omega⟩).snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨i, hlt'⟩).2)
    : (findValidMonthDay_n dt.Year isLeap i ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩
            hl hle' hlt hlt' hydn hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_n dt.Year isLeap i ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩
            hl hle' hlt hlt' hydn hyd).Day
           := by
  simp [findValidMonthDay_n]
  simp [Icc, Subtype.ext_iff]
  have := incr_of_day_in_intervall dt ml h
  simp at hydn
  rw [← heq] at hydn
  rw [← heq] at hyd
  have := dy'_month_n_and_day_eq dt isLeap ⟨i, hlt'⟩ hle' hl hml h hydn hyd
  simp_all

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
      exact findValidMonthDay_n_month_eq isLeap 1 yd
                    (by simp) (by simp_all) (by simp_all)
                    hl hml h heq hle hne hyd
    · split
      · rename_i hne' hne hyd
        exact findValidMonthDay_n_month_eq isLeap 2 yd
                    (by simp) (by simp_all) (by simp_all)
                    hl hml h heq hle hne hyd
      · split
        · rename_i hne hyd
          exact findValidMonthDay_n_month_eq isLeap 3 yd
                    (by simp) (by simp_all) (by simp_all)
                    hl hml h heq hle hne hyd
        · split
          · rename_i hne hyd
            exact findValidMonthDay_n_month_eq isLeap 4 yd
                          (by simp) (by simp_all) (by simp_all)
                          hl hml h heq hle hne hyd
          · split
            · rename_i hne hyd
              exact findValidMonthDay_n_month_eq isLeap 5 yd
                            (by simp) (by simp_all) (by simp_all)
                            hl hml h heq hle hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact findValidMonthDay_n_month_eq isLeap 6 yd
                              (by simp) (by simp_all) (by simp_all)
                              hl hml h heq hle hne hyd
              · split
                · rename_i hne hyd
                  exact findValidMonthDay_n_month_eq isLeap 7 yd
                                (by simp) (by simp_all) (by simp_all)
                                hl hml h heq hle hne hyd
                · split
                  · rename_i hne hyd
                    exact findValidMonthDay_n_month_eq isLeap 8 yd
                                  (by simp) (by simp_all) (by simp_all)
                                  hl hml h heq hle hne hyd
                  · split
                    · rename_i hne hyd
                      exact findValidMonthDay_n_month_eq isLeap 9 yd
                                    (by simp) (by simp_all) (by simp_all)
                                    hl hml h heq hle hne hyd
                    · split
                      · rename_i hne hyd
                        exact findValidMonthDay_n_month_eq isLeap 10 yd
                                      (by simp) (by simp_all) (by simp_all)
                                      hl hml h heq hle hne hyd
                      · rename_i hne
                        have hyd : yd.val + 1 ≤  (monthLastDayAsDayOfYear isLeap)[11].2 := by
                          have : (monthLastDayAsDayOfYear isLeap)[11].2
                               = if isLeap then 366 else 365 := by
                            cases isLeap <;> decide
                          simp_all
                        exact findValidMonthDay_n_month_eq isLeap 11 yd
                                      (by simp) (by simp_all) (by simp_all)
                                      hl hml h heq hle hne hyd

theorem monthLengths_month_1_eq_31_ne (isleap : Bool)
    : ∀ a ∈ monthLengths isleap, ¬31 = a.2 → ¬a.1 = 1 := by
  cases isleap <;> simp [monthLengths]

theorem monthLengths_month_1_eq_31 (isleap : Bool)
  (a : { x // x ∈ monthLengths isleap}) (h : a.val.1 = 1)
    : a.val.2 = 31 := by
  by_contra
  have := monthLengths_month_1_eq_31_ne isleap a a.property (by omega)
  contradiction

theorem findValidMonthDay_n_month_eq_incr {dt : Date} (isLeap : Bool) (i : Nat) (yd : Time.Icc 1 366)
  (hle' : 1 ≤ i)
  (hlt : i < (monthLengths isLeap).length)
  (hlt' : i < (monthLastDayAsDayOfYear isLeap).length)
  (hl : isLeapYear dt.Year = isLeap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hydn : ¬yd.val + 1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨i-1, by omega⟩).snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨i, hlt'⟩).2)
    : (findValidMonthDay_n dt.Year isLeap i ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩
            hl hle' hlt hlt' hydn hyd).Month
        = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_n dt.Year isLeap i ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩
            hl hle' hlt hlt' hydn hyd).Day
        = ⟨1, by simp⟩
           := by
  simp [findValidMonthDay_n]
  simp [Icc, Subtype.ext_iff]
  simp at hydn
  rw [← heq] at hydn
  rw [← heq] at hyd
  have := dy'_month_n_and_day_eq_incr dt isLeap ⟨i, hlt'⟩ hle' hl hml h hydn hyd
  exact And.intro
    (by simp_all)
    (by have := this.right; simp_all)

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
  · split
    · rename_i hne hyd
      exact findValidMonthDay_n_month_eq_incr isLeap 1 yd
                  (by simp) (by simp_all) (by simp_all)
                  hl hml h hm heq hle hne hyd
    · split
      · rename_i hne hyd
        exact findValidMonthDay_n_month_eq_incr isLeap 2 yd
                    (by simp) (by simp_all) (by simp_all)
                    hl hml h hm heq hle hne hyd
      · split
        · rename_i hne hyd
          exact findValidMonthDay_n_month_eq_incr isLeap 3 yd
                      (by simp) (by simp_all) (by simp_all)
                      hl hml h hm heq hle hne hyd
        · split
          · rename_i hne hyd
            exact findValidMonthDay_n_month_eq_incr isLeap 4 yd
                        (by simp) (by simp_all) (by simp_all)
                        hl hml h hm heq hle hne hyd
          · split
            · rename_i hne hyd
              exact findValidMonthDay_n_month_eq_incr isLeap 5 yd
                          (by simp) (by simp_all) (by simp_all)
                          hl hml h hm heq hle hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact findValidMonthDay_n_month_eq_incr isLeap 6 yd
                            (by simp) (by simp_all) (by simp_all)
                            hl hml h hm heq hle hne hyd
              · split
                · rename_i hne hyd
                  exact findValidMonthDay_n_month_eq_incr isLeap 7 yd
                              (by simp) (by simp_all) (by simp_all)
                              hl hml h hm heq hle hne hyd
                · split
                  · rename_i hne hyd
                    exact findValidMonthDay_n_month_eq_incr isLeap 8 yd
                                (by simp) (by simp_all) (by simp_all)
                                hl hml h hm heq hle hne hyd
                  · split
                    · rename_i hne hyd
                      exact findValidMonthDay_n_month_eq_incr isLeap 9 yd
                                  (by simp) (by simp_all) (by simp_all)
                                  hl hml h hm heq hle hne hyd
                    · split
                      · rename_i hne hyd
                        exact findValidMonthDay_n_month_eq_incr isLeap 10 yd
                                    (by simp) (by simp_all) (by simp_all)
                                    hl hml h hm heq hle hne hyd
                      · rename_i hne
                        have hyd : yd.val + 1 ≤  (monthLastDayAsDayOfYear isLeap)[11].2 := by
                          have : (monthLastDayAsDayOfYear isLeap)[11].2
                               = if isLeap then 366 else 365 := by
                            cases isLeap <;> decide
                          simp_all
                        exact findValidMonthDay_n_month_eq_incr isLeap 11 yd
                                    (by simp) (by simp_all) (by simp_all)
                                    hl hml h hm heq hle hne hyd
