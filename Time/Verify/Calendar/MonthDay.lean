import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.OrdinalDate
import Time.Verify.Calendar.MonthLength
import Time.Verify.Calendar.DayOfYear

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

theorem dateToOrdinalDate'_dateToOrdinalDate_eq {dt : Date}
    : dateToOrdinalDate' dt = dateToOrdinalDate dt := by
  simp [dateToOrdinalDate', dateToOrdinalDate]
  split <;> simp

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
  unfold OrdinalDate.next_date OrdinalDate.DayOfYear.incr dateToOrdinalDate'
  split <;> simp_all
  · split <;> try simp_all
    · rename_i h _ _ heq
      simp [h] at heq
    · simp [OrdinalDate.ext_iff]
      split <;> try simp_all
      · rename_i h' dy' _ heq'' dy hdy heq'
        have : dy < 365 := by
          have := dy_lt_of_day_or_month_lt h
          simp_all
        split
        · have := dateToOrdinalDate_year_eq dt
          simp [And]
          simp [h'] at heq''
          simp [Icc, Subtype.ext] at heq''
          simp [dateToOrdinalDate, h'] at heq
          simp [OrdinalDate.ext_iff] at heq
          have := heq.right
          rw [heq'] at this
          simp_all
        · contradiction
      · rename_i h' dy' _ heq'' dy hdy heq'
        have : dy < 366 := by
          have := dy_lt_of_day_or_month_lt h
          simp_all
        split
        · have := dateToOrdinalDate_year_eq dt
          simp [And]
          simp [h'] at heq''
          simp [Icc, Subtype.ext] at heq''
          simp [Icc, Subtype.ext]
          rw [← heq'']
          simp [dateToOrdinalDate, h] at heq
          simp [OrdinalDate.ext_iff] at heq
          have := heq.right
          rw [heq'] at this
          simp_all
          simp [Icc, Subtype.ext] at this
          exact this.symm
        · contradiction
  · split <;> try simp_all
    · rename_i h yd _ heq
      simp [h] at heq
      simp [Icc, Subtype.ext] at heq
      simp [OrdinalDate.ext_iff]
      split <;> simp_all
      · split
        · have := dateToOrdinalDate_year_eq dt
          simp [And]
          rw [this]
          simp
          simp [Icc, Subtype.ext]
          rename_i heq''' _ _ yd' _ heq'' _
          simp [← heq]
          simp [heq'''] at heq''
          simp [dateToOrdinalDate, h] at heq''
          simp [Icc, Subtype.ext] at heq''
          simp [heq'']
        · rename_i h' heq'' _ _ yd _ heq' _
          simp [heq''] at heq'
          simp [dateToOrdinalDate ] at heq'
          simp [h] at heq'
          simp [Icc, Subtype.ext] at heq'
          have : dy' false dt.Month dt.Day < 365 := by
            cases h'
            · rename_i h'
              have := @dy'_hlt' dt ml h'
              simp [h] at this
              exact this
            · rename_i h'
              have := @dy'_lt_of_month_lt dt h'
              simp [h] at this
              exact this
          rw [heq'] at this
          contradiction
      · rename_i heq'' _ _ _ _ heq'
        simp [heq''] at heq'
        simp [dateToOrdinalDate ] at heq'
        simp [h] at heq'
    · rename_i h _ _ heq
      simp [h] at heq

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
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
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

theorem findValidMonthDay_2_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[0].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨1, by simp⟩).2)
    : (findValidMonthDay_2 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_2 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_2]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_2_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_2_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_2_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_2_day_eq dt false (by omega) hne hyd
    simp_all

theorem findValidMonthDay_3_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[1].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨2, by simp⟩).2)
    : (findValidMonthDay_3 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_3 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_3]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_2_if_lt true hml (by simp_all) hl)
    simp [dy'_month_3_eq dt true (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_3_day_eq dt true (by omega) this hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_2_if_lt false hml (by simp_all) hl)
    simp [dy'_month_3_eq dt false (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_3_day_eq dt false (by omega) this hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq`. -/
theorem findValidMonthDay_4_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[2].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨3, by simp⟩).2)
    : (findValidMonthDay_4 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_4 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_4]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_4_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_4_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_4_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_4_day_eq dt false (by omega) hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq'`. -/
theorem findValidMonthDay_5_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[3].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨4, by simp⟩).2)
    : (findValidMonthDay_5 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_5 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_5]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_4_if_lt true hml (by simp_all) hl)
    simp [dy'_month_5_eq dt true (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_5_day_eq dt true (by omega) this hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_4_if_lt false hml (by simp_all) hl)
    simp [dy'_month_5_eq dt false (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_5_day_eq dt false (by omega) this hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq`. -/
theorem findValidMonthDay_6_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[4].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨5, by simp⟩).2)
    : (findValidMonthDay_6 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_6 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_6]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_6_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_6_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_6_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_6_day_eq dt false (by omega) hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq'`. -/
theorem findValidMonthDay_7_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[5].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨6, by simp⟩).2)
    : (findValidMonthDay_7 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_7 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_7]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_6_if_lt true hml (by simp_all) hl)
    simp [dy'_month_7_eq dt true (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_7_day_eq dt true (by omega) this hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_6_if_lt false hml (by simp_all) hl)
    simp [dy'_month_7_eq dt false (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_7_day_eq dt false (by omega) this hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq`. -/
theorem findValidMonthDay_8_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[6].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨7, by simp⟩).2)
    : (findValidMonthDay_8 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_8 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_8]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_8_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_8_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_8_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_8_day_eq dt false (by omega) hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq`. -/
theorem findValidMonthDay_9_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[7].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨8, by simp⟩).2)
    : (findValidMonthDay_9 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_9 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_9]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_9_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_9_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_9_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_9_day_eq dt false (by omega) hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq'`. -/
theorem findValidMonthDay_10_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[8].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨9, by simp⟩).2)
    : (findValidMonthDay_10 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_10 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_10]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_9_if_lt true hml (by simp_all) hl)
    simp [dy'_month_10_eq dt true (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_10_day_eq dt true (by omega) this hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    have := (month_9_if_lt false hml (by simp_all) hl)
    simp [dy'_month_10_eq dt false (by omega) this hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_10_day_eq dt false (by omega) this hne hyd
    simp_all

/-- Generated by `gen_findValidMonthDay_month_eq`. -/
theorem findValidMonthDay_11_month_eq {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hle : yd.val + 1 ≤ if isLeap then 366 else 365)
  (hl : isLeapYear dt.Year = isLeap)
  (hne : ¬yd.val + 1 ≤ (monthLastDayAsDayOfYear isLeap)[9].snd)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨10, by simp⟩).2)
    : (findValidMonthDay_11 dt.Year isLeap ⟨yd + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Month
        = dt.Month
      ∧ ⟨dt.Day.val + 1, incr_of_day_in_intervall dt ml h⟩
        = (findValidMonthDay_11 dt.Year isLeap ⟨yd.val + 1, incr_of_yd_in yd isLeap hle⟩ hl hne hyd).Day
           := by
  simp [findValidMonthDay_11]
  simp [Icc, Subtype.ext_iff]
  simp [monthLastDayAsDayOfYear] at hyd
  have := incr_of_day_in_intervall dt ml h
  split at hyd <;> simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_11_eq dt true (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_11_day_eq dt true (by omega) hne hyd
    simp_all
  · simp [monthLastDayAsDayOfYear] at hne
    rw [← heq] at hne
    rw [← heq] at hyd
    simp [dy'_month_11_eq dt false (by omega) hne hyd]
    simp [monthLastDayAsDayOfYear]
    have := dy'_month_11_day_eq dt false (by omega) hne hyd
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
    exact findValidMonthDay_1_month_eq isLeap yd hml h heq hle hyd
  · split
    . rename_i hne hyd
      exact findValidMonthDay_2_month_eq isLeap yd hml h heq hle hl hne hyd
    · split
      · rename_i hne' hne hyd
        exact findValidMonthDay_3_month_eq isLeap yd hml h heq hle hl hne hyd
      · split
        · rename_i hne hyd
          exact findValidMonthDay_4_month_eq isLeap yd hml h heq hle hl hne hyd
        · split
          · rename_i hne hyd
            exact findValidMonthDay_5_month_eq isLeap yd hml h heq hle hl hne hyd
          · split
            · rename_i hne hyd
              exact findValidMonthDay_6_month_eq isLeap yd hml h heq hle hl hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact findValidMonthDay_7_month_eq isLeap yd hml h heq hle hl hne hyd
              · split
                · rename_i hne hyd
                  exact findValidMonthDay_8_month_eq isLeap yd hml h heq hle hl hne hyd
                · split
                  · rename_i hne hyd
                    exact findValidMonthDay_9_month_eq isLeap yd hml h heq hle hl hne hyd
                  · split
                    · rename_i hne hyd
                      exact findValidMonthDay_10_month_eq isLeap yd hml h heq hle hl hne hyd
                    · split
                      · rename_i hne hyd
                        exact findValidMonthDay_11_month_eq isLeap yd hml h heq hle hl hne hyd
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

theorem findValidMonthDay_2_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : 31 ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 59 else 58)
    : dt.Month.val = 1 ∧ yd.val = 31 := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_1_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_1_eq_snd dt isLeap a this h1 h2
  simp_all

theorem findValidMonthDay_2_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨0, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨1, by simp⟩).2)
    : (findValidMonthDay_2 dt.Year isLeap ⟨yd + 1,
          by cases isLeap <;> simp_arith [monthLastDayAsDayOfYear] at hyd <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_2 dt.Year isLeap ⟨yd + 1,
          by cases isLeap <;> simp_arith [monthLastDayAsDayOfYear] at hyd <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_2]
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
      simp [findValidMonthDay_2_month_eq_incr' true yd hml h heq hl (by omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp [findValidMonthDay_2_month_eq_incr' false yd hml h heq hl (by omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_3_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 60 else 59) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 90 else 89)
    : dt.Month.val = 2 ∧ yd.val = (if isLeap then 60 else 59) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_2_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_2_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_3_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨1, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨2, by simp⟩).2)
    : (findValidMonthDay_3 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_3 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_3]
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
      simp_all [findValidMonthDay_3_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_3_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_4_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 91 else 90) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 120 else 119)
    : dt.Month.val = 3 ∧ yd.val = (if isLeap then 91 else 90) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_3_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_3_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_4_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨2, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨3, by simp⟩).2)
    : (findValidMonthDay_4 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_4 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_4]
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
      simp_all [findValidMonthDay_4_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_4_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_5_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 121 else 120) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 151 else 150)
    : dt.Month.val = 4 ∧ yd.val = (if isLeap then 121 else 120) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_4_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_4_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_5_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨3, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨4, by simp⟩).2)
    : (findValidMonthDay_5 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_5 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_5]
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
      simp_all [findValidMonthDay_5_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_5_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_6_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 152 else 151) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 181 else 180)
    : dt.Month.val = 5 ∧ yd.val = (if isLeap then 152 else 151) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_5_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_5_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_6_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨4, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨5, by simp⟩).2)
    : (findValidMonthDay_6 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_6 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_6]
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
      simp_all [findValidMonthDay_6_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_6_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_7_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 182 else 181) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 212 else 211)
    : dt.Month.val = 6 ∧ yd.val = (if isLeap then 182 else 181) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_6_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_6_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_7_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨5, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨6, by simp⟩).2)
    : (findValidMonthDay_7 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_7 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_7]
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
      simp_all [findValidMonthDay_7_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_7_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_8_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 213 else 212) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 243 else 242)
    : dt.Month.val = 7 ∧ yd.val = (if isLeap then 213 else 212) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_7_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_7_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_8_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨6, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨7, by simp⟩).2)
    : (findValidMonthDay_8 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_8 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_8]
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
      simp_all [findValidMonthDay_8_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_8_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_9_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 244 else 243) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 273 else 272)
    : dt.Month.val = 8 ∧ yd.val = (if isLeap then 244 else 243) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_8_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_8_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_9_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨7, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨8, by simp⟩).2)
    : (findValidMonthDay_9 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_9 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_9]
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
      simp_all [findValidMonthDay_9_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_9_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_10_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 274 else 273) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 304 else 303)
    : dt.Month.val = 9 ∧ yd.val = (if isLeap then 274 else 273) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_9_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_9_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_10_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨8, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨9, by simp⟩).2)
    : (findValidMonthDay_10 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_10 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_10]
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
      simp_all [findValidMonthDay_10_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_10_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

/-- Generated by `gen_findValidMonthDay_month_eq_incr'`. -/
theorem findValidMonthDay_11_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 305 else 304) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap then 334 else 333)
    : dt.Month.val = 10 ∧ yd.val = (if isLeap then 305 else 304) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_month_10_eq_snd_le dt isLeap a h1 h2
  have := monthLastDayAsDayOfYear'_month_10_eq_snd dt isLeap a this h1 h2
  simp_all

/-- Generated by `gen_findValidMonthDay_month_eq_incr`. -/
theorem findValidMonthDay_11_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap)
  (hn : ¬yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨9, by simp⟩).2)
  (hyd : yd.val+1 ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨10, by simp⟩).2)
    : (findValidMonthDay_11 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Month = ⟨dt.Month.val + 1, by omega⟩
      ∧ (findValidMonthDay_11 dt.Year isLeap ⟨yd + 1,
          by have := dy'_lt_of_month_lt hm; cases isLeap <;> simp_all <;> omega⟩
          hl hn hyd).Day = ⟨1, by omega⟩ := by
  simp [findValidMonthDay_11]
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
      simp_all [findValidMonthDay_11_month_eq_incr' true yd hml h heq hl (by simp_all; omega) (by simp_all)]
    · contradiction
  · simp [] at hyd
    simp [monthLastDayAsDayOfYear] at hn
    split at hn
    · contradiction
    · simp [] at hn
      simp [monthLastDayAsDayOfYear]
      split <;> simp_all
      rw [← hml] at h
      simp_all [findValidMonthDay_11_month_eq_incr' false yd hml h heq hl (by simp_all; omega) (by simp_all)]

theorem findValidMonthDay_12_month_eq_incr' {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val) (hl : isLeapYear dt.Year = isLeap)
  (h1 : (if isLeap then 335 else 334) ≤ yd.val)
  (h2 : yd.val ≤ if isLeap = true then 365 else 364)
    : dt.Month.val = 11 ∧ yd.val = (if isLeap then 335 else 334) := by
  simp [dy'] at heq
  let a := memOfMonth isLeap dt.Month
  have : a = memOfMonth isLeap dt.Month := by simp
  rw [← this] at heq
  have := yd_eq_monthLastDayAsDayOfYear'_val isLeap yd hml h ml.property heq hl
  rw  [← this] at h1
  rw  [← this] at h2
  rw [← a.property.right]
  have := monthLastDayAsDayOfYear'_sub_le_31 isLeap a a.property.left
  have := monthLastDayAsDayOfYear'_month_11_eq_snd_le dt isLeap a h1 (by omega)
  have := monthLastDayAsDayOfYear'_month_11_eq_snd dt isLeap a this h1 (by omega)
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
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap) (hle : yd.val+1 ≤ if isLeap then 366 else 365)
    : 1 ≤ yd.val + 1 ∧ yd.val + 1 ≤ 366 := by
  simp [hle]
  have := @dy'_lt_of_month_lt dt hm
  simp [heq, hl] at this
  cases isLeap <;> simp_all
  omega

theorem findValidMonthDay_month_eq_incr {dt : Date} (isLeap : Bool) (yd : Time.Icc 1 366)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (hm : dt.Month.val < 12)
  (heq : Time.dy' isLeap dt.Month dt.Day = yd.val)
  (hl : isLeapYear dt.Year = isLeap) (hle : yd.val+1 ≤ if isLeap then 366 else 365)
    : (findValidMonthDay dt.Year isLeap ⟨yd+1, yd_add_one_lt isLeap yd hml hm heq hl hle⟩
        hl hle).Month
    = ⟨dt.Month.val + 1, by omega⟩
    ∧ (findValidMonthDay dt.Year isLeap ⟨yd+1, yd_add_one_lt isLeap yd hml hm heq hl
          hle⟩ hl hle).Day
    = ⟨1, by simp⟩ := by
  unfold findValidMonthDay
  split
  · rename_i hyd
    exact findValidMonthDay_1_month_eq_incr isLeap yd hml h hm heq hl hyd
  · split
    · rename_i hne hyd
      exact findValidMonthDay_2_month_eq_incr isLeap yd hml h hm heq hl hne hyd
    · split
      · rename_i hne hyd
        exact findValidMonthDay_3_month_eq_incr isLeap yd hml h hm heq hl hne hyd
      · split
        · rename_i hne hyd
          exact findValidMonthDay_4_month_eq_incr isLeap yd hml h hm heq hl hne hyd
        · split
          · rename_i hne hyd
            exact findValidMonthDay_5_month_eq_incr isLeap yd hml h hm heq hl hne hyd
          · split
            · rename_i hne hyd
              exact findValidMonthDay_6_month_eq_incr isLeap yd hml h hm heq hl hne hyd
            · simp [findValidMonthDay_tail]
              split
              · rename_i hne hyd
                exact findValidMonthDay_7_month_eq_incr isLeap yd hml h hm heq hl hne hyd
              · split
                · rename_i hne hyd
                  exact findValidMonthDay_8_month_eq_incr isLeap yd hml h hm heq hl hne hyd
                · split
                  · rename_i hne hyd
                    exact findValidMonthDay_9_month_eq_incr isLeap yd hml h hm heq hl hne hyd
                  · split
                    · rename_i hne hyd
                      exact findValidMonthDay_10_month_eq_incr isLeap yd hml h hm heq hl hne hyd
                    · split
                      · rename_i hne hyd
                        exact findValidMonthDay_11_month_eq_incr isLeap yd hml h hm heq hl hne hyd
                      · rename_i hne
                        exact findValidMonthDay_12_month_eq_incr isLeap yd hml h hm heq hl hne hle
