import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.OrdinalDate
import Time.Verify.Calendar.MonthLength
import Time.Verify.Calendar.MonthDay
import Time.Verify.Calendar.DayOfYear

namespace Verify

/-!
## Verify date calculations

Main theorems:

* `Verify.Gregorian.next_date_eq_next_date`,
* `Verify.Gregorian.next_date_eq_add_one`,
* `Verify.Gregorian.next_date_eq_mjd_add_one`.

-/

namespace Gregorian

open Time
open Time.Notation
open Verify.MonthLength
open Verify.MonthDay
open Verify.DayOfYear

/-- Get next_date of `dt`:

*  if `dt.Day` is less then days in `dt.Month` then add 1 to `dt.Day`,
*  else if `dt.Month` less then 12 then add 1 to `dt.Month` and set `dt.Day` to 1,
*  else add 1 to `dt.Year` and set `dt.Day` and `dt.Month` to 1.

See [UTC Time, Formally Verified](https://arxiv.org/abs/2209.14227). -/
def next_date (dt : Date) : Date :=
  let ml := monthLengths_of_date dt
  if h : dt.Day.val < ml.val.snd then
    {dt with Day := ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩,
             IsValid := incr_of_day_is_valid dt ml h}
  else if h : dt.Month.1 < 12 then
    {dt with Day := ⟨1, by simp⟩, Month := ⟨dt.Month.1 + 1, by omega⟩,
             IsValid := incr_of_month_is_valid dt h}
  else
    {dt with Year := dt.Year + 1, Day := ⟨1, by simp⟩, Month := ⟨1, by simp⟩,
             IsValid := ⟨(1, 31), by simp [Time.monthLengths]⟩ }

/-- the modified julian day of day 1858-11-17 should have value zero. -/
theorem zero_of_modified_julian_day_eq : fromGregorian (date% 1858-11-17) == ⟨0⟩ := by rfl

/-- the default values of `Date` and `Day` are january 1 of year 1 and should be equal. -/
theorem default_of_modified_julian_day_eq : fromGregorian default == default := by rfl

theorem next_date_of_day_lt_eq' {dt : Date} {dy : Nat}
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' false dt.Month dt.Day = dy)
  (hl : isLeapYear dt.Year = false)
    : {dt with Day := ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩,
               IsValid := incr_of_day_is_valid dt ml h}
    = ordinalDateToDate
        { year := dt.Year,
          dayOfYear := DayOfYear.common ⟨dy + 1, by have := dy'_add_one_hle h; simp_all⟩,
          isValid := (by simp_all) } := by
  simp [ordinalDateToDate, Date.ext_iff, findValidMonthDay_year_eq]
  let yd : Icc 1 366 := ⟨dy, by
          rw [← heq]
          simp [Time.le_dy' false dt.Month dt.Day]
          have := Time.dy'_le false dt.Month dt.Day
          split at this <;> simp_all
          omega⟩
  simp +zetaDelta [findValidMonthDay_month_eq false yd hml h heq hl (by
          have := dy'_add_one_hle h
          simp [hl] at this
          simp_all +zetaDelta)]

theorem next_date_of_day_lt_eq'' {dt : Date} {dy : Nat}
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' true dt.Month dt.Day = dy)
  (hl : isLeapYear dt.Year = true)
    : {dt with Day := ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩,
               IsValid := incr_of_day_is_valid dt ml h}
    = ordinalDateToDate
        { year := dt.Year,
          dayOfYear := DayOfYear.leap ⟨dy + 1, by have := dy'_add_one_hle h; simp_all⟩,
          isValid := (by simp_all) } := by
  simp [ordinalDateToDate, Date.ext_iff, findValidMonthDay_year_eq]
  let yd : Icc 1 366 := ⟨dy, by
          rw [← heq]
          simp [Time.le_dy' true dt.Month dt.Day]
          have := Time.dy'_le true dt.Month dt.Day
          split at this <;> simp_all⟩
  simp +zetaDelta [findValidMonthDay_month_eq true yd hml h heq hl (by
          have := dy'_add_one_hle h
          simp [hl] at this
          simp_all +zetaDelta)]

theorem next_date_of_day_lt_eq (dt : Date)
  (ml : { m // monthLengthsOfDate m dt })
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
    : {dt with Day := ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩,
               IsValid := incr_of_day_is_valid dt ml h}
    = ordinalDateToDate (OrdinalDate.next_date (dateToOrdinalDate dt)) := by
  generalize heq : dateToOrdinalDate dt = dt'
  have := @next_date_of_day_lt_eq_incr' dt dt' ml (Or.inl h) heq.symm
  rw [← this]
  simp only [dateToOrdinalDate', OrdinalDate.DayOfYear.incr]
  split
  · rename_i dy hdy heq
    split at heq
    · simp [Icc, Subtype.ext_iff] at heq
    · simp [Icc, Subtype.ext_iff] at heq
      exact next_date_of_day_lt_eq' hml h heq (by simp_all)
  · rename_i dy hdy heq
    split at heq
    · simp [Icc, Subtype.ext_iff] at heq
      exact next_date_of_day_lt_eq'' hml h heq (by simp_all)
    · simp [Icc, Subtype.ext_iff] at heq

theorem next_date_of_last_day_of_month_eq' {dt : Date} {dy : Nat}
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' false dt.Month dt.Day = dy)
  (hl : isLeapYear dt.Year = false)
    : {dt with Month := ⟨dt.Month.val + 1, by omega⟩
               Day := ⟨1, simp⟩,
               IsValid := incr_of_month_is_valid dt hm}
    = ordinalDateToDate
        { year := dt.Year,
          dayOfYear := DayOfYear.common ⟨dy + 1, by
            have := @dy'_lt_of_month_lt dt hm
            simp [hl] at this
            omega⟩,
          isValid := (by simp_all) } := by
  simp [ordinalDateToDate, Date.ext_iff, findValidMonthDay_year_eq]
  let yd : Icc 1 366 := ⟨dy, by
          rw [← heq]
          simp [Time.le_dy' false dt.Month dt.Day]
          have := Time.dy'_le false dt.Month dt.Day
          split at this <;> simp_all
          omega⟩
  simp +zetaDelta [findValidMonthDay_month_eq_incr false yd hml h hm heq hl
    (by
      have := dy'_lt_of_month_lt hm
      simp [hl] at this
      simp_all +zetaDelta
      exact Nat.le_of_lt_succ this)]

theorem next_date_of_last_day_of_month_eq'' {dt : Date} {dy : Nat}
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' true dt.Month dt.Day = dy)
  (hl : isLeapYear dt.Year = true)
    : {dt with Month := ⟨dt.Month.val + 1, by omega⟩
               Day := ⟨1, simp⟩,
               IsValid := incr_of_month_is_valid dt hm}
    = ordinalDateToDate
        { year := dt.Year,
          dayOfYear := DayOfYear.leap ⟨dy + 1, by
            have := @dy'_lt_of_month_lt dt hm
            simp [hl] at this
            omega⟩,
          isValid := (by simp_all) } := by
  simp [ordinalDateToDate, Date.ext_iff, findValidMonthDay_year_eq]
  let yd : Icc 1 366 := ⟨dy, by
          rw [← heq]
          simp [Time.le_dy' true dt.Month dt.Day]
          have := Time.dy'_le true dt.Month dt.Day
          split at this <;> simp_all⟩
  simp +zetaDelta [findValidMonthDay_month_eq_incr true yd hml h hm heq hl
    (by
      have := dy'_lt_of_month_lt hm
      simp [hl] at this
      simp_all +zetaDelta
      exact Nat.le_of_lt_succ this)]

theorem next_date_of_last_day_of_month_eq (dt : Date)
  (ml : { m // monthLengthsOfDate m dt })
  (hml : ml = monthLengths_of_date dt) (h : ¬dt.Day.val < ml.val.snd)
  (hm : dt.Month.val < 12)
    : {dt with Month := ⟨dt.Month.val + 1, by omega⟩
               Day := ⟨1, simp⟩,
               IsValid := incr_of_month_is_valid dt hm}
    = ordinalDateToDate (OrdinalDate.next_date (dateToOrdinalDate dt)) := by
  simp [monthLengthsOfDate] at ml
  have h : dt.Day.val = ml.val.snd := by omega
  generalize heq : dateToOrdinalDate dt = dt'
  have := @next_date_of_day_lt_eq_incr' dt dt' ml (Or.inr hm) heq.symm
  rw [← this]
  simp only [dateToOrdinalDate', OrdinalDate.DayOfYear.incr]
  split
  · rename_i dy hdy heq
    split at heq
    · simp [Icc, Subtype.ext_iff] at heq
    · simp [Icc, Subtype.ext_iff] at heq
      exact next_date_of_last_day_of_month_eq' hml h hm heq (by simp_all)
  · rename_i dy hdy heq
    split at heq
    · simp [Icc, Subtype.ext_iff] at heq
      exact next_date_of_last_day_of_month_eq'' hml h hm heq (by simp_all)
    · simp [Icc, Subtype.ext_iff] at heq

theorem dy'_of_last_day_of_year (dt : Date)
  (ml : { m //monthLengthsOfDate m dt })
  (hml : ml = monthLengths_of_date dt) (h1 : ¬dt.Day.val < ml.val.snd) (h2 : ¬dt.Month.val < 12)
    : dy' (isLeapYear dt.Year) dt.Month dt.Day
    = if isLeapYear dt.Year then 366 else 365 := by
  have h2 : dt.Month.val = 12 := by
    have := dt.Month.property.right
    omega
  simp [dy']
  generalize memOfMonth (isLeapYear dt.Year) dt.Month = a
  simp_all
  have heq : a.val.fst = 12 := by omega
  have hv : a.val.snd.fst = if isLeapYear dt.Year = true then 336 else 335 := by
    have hp := a.property.left
    simp_arith [monthLastDayAsDayOfYear'] at hp
    split at hp
    · simp_all
      have : a.val = (12, 336, 366) := by
        simp [Prod.ext_iff] at hp
        rw [heq] at hp
        simp at hp
        have h2 := hp.left
        have h3 := hp.right
        simp [Prod.ext_iff]
        simp_all
      simp [this]
    · simp_all
      have : a.val = (12, 335, 365) := by
        simp [Prod.ext_iff] at hp
        rw [heq] at hp
        simp at hp
        have h2 := hp.left
        have h3 := hp.right
        simp [Prod.ext_iff]
        simp_all
      simp [this]
  have : dt.Day.val = 31 := by
    generalize monthLengths_of_date dt = a at h1
    simp [monthLengthsOfDate] at a
    have hp := a.property.left
    simp_arith [monthLengths, Prod.ext_iff] at hp
    have heq : a.val.fst = 12 := by omega
    rw [heq] at hp
    simp at hp
    rw [hp] at h1
    omega
  simp_all
  split <;> omega

theorem next_date_of_last_day_of_year_eq (dt : Date)
  (ml : { m // monthLengthsOfDate m dt })
  (hml : ml = monthLengths_of_date dt) (h1 : ¬dt.Day.val < ml.val.snd)
  (h2 : ¬dt.Month.val < 12)
    : {dt with Year := dt.Year + 1, Month := ⟨1, by simp⟩, Day := ⟨1, by simp⟩,
               IsValid := ⟨(1, 31), by simp_arith [monthLengths]⟩}
    = ordinalDateToDate (OrdinalDate.next_date (dateToOrdinalDate dt)) := by
  simp [dateToOrdinalDate, monthAndDayToDayOfYearClipped, monthAndDayToDayOfYearClipped']
  have : isLeapYear dt.Year = true ∨ ¬isLeapYear dt.Year = true := by simp
  cases this
  · rename_i h
    simp [h]
    have := dy'_of_last_day_of_year dt ml hml h1 h2
    rw [← dy_eq_dy'] at this
    simp [h] at this
    simp_all
    simp [OrdinalDate.next_date]
    split
    · simp [ordinalDateToDate, findValidMonthDay, monthLastDayAsDayOfYear,
            findValidMonthDay_1]
    · simp [ordinalDateToDate, findValidMonthDay, monthLastDayAsDayOfYear,
            findValidMonthDay_1]
  · rename_i h
    simp [h]
    have := dy'_of_last_day_of_year dt ml hml h1 h2
    rw [← dy_eq_dy'] at this
    simp [h] at this
    simp_all
    simp [OrdinalDate.next_date]
    split <;> simp [ordinalDateToDate, findValidMonthDay, monthLastDayAsDayOfYear,
                    findValidMonthDay_1]

/-- `Verify.Gregorian.next_date` transforms to `Verify.OrdinalDate.next_date` -/
theorem next_date_eq_next_date (dt : Date)
    : next_date dt = (dateToOrdinalDate dt |> OrdinalDate.next_date |> ordinalDateToDate) := by
  let ml := monthLengths_of_date dt
  simp [next_date]
  split
  · rename_i h
    exact next_date_of_day_lt_eq dt ml rfl h
  · split
    · rename_i h' h
      exact next_date_of_last_day_of_month_eq dt ml rfl h' h
    · rename_i h' h
      exact next_date_of_last_day_of_year_eq dt ml rfl h' h

/-- `Verify.Gregorian.next_date` transforms to `Time.Day.addDays` 1. -/
theorem next_date_eq_mjd_add_one (dt : Date)
    : next_date dt =
       (dateToOrdinalDate dt |> fromOrdinalDate
       |> Day.addDays 1 |> toOrdinalDate |> ordinalDateToDate) := by
  have := next_date_eq_next_date dt
  have := OrdinalDate.next_date_eq_mjd_add_one (dateToOrdinalDate dt)
  simp_all

/-- `Verify.Gregorian.next_date` equals to `Time.Gregorian.addDays` 1. -/
theorem next_date_eq_add_one (dt : Date) : next_date dt = Gregorian.addDays 1 dt := by
  rw [Gregorian.addDays]
  rw [next_date_eq_next_date]
  rw [OrdinalDate.next_date_eq_add_one]
