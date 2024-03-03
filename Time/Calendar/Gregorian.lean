import Time.Calendar.Days
import Time.Calendar.OrdinalDate
import Time.Calendar.MonthDay
import Time.Calendar.CalendarDiffDays

namespace Time

open Private

/--  Convert to proleptic Gregorian calendar. -/
def toGregorian (date : Day) : Date :=
  ordinalDateToDate (toOrdinalDate date)

/-- Convert from proleptic Gregorian calendar. -/
def fromGregorianDate (dt : Date) : Day :=
  let dy := monthAndDayToDayOfYear (isLeapYear dt.Year) dt.Month dt.Day
  fromOrdinalDayOfYear dt.Year dy

/-- Convert from proleptic Gregorian calendar.
Invalid values will be clipped to the correct range, month first, then day. -/
def fromGregorian (year : Int) (month : Int) (day : Int) : Day :=
  let dy := monthAndDayToDayOfYear (isLeapYear year) month day
  fromOrdinalDayOfYear year dy

/-- Convert from proleptic Gregorian calendar. Invalid values give result none. -/
def fromGregorianValid (year : Int) (month : Int) (day : Int) : Option Day := do
  let day ← monthAndDayToDayOfYearValid (isLeapYear year) month day
  fromOrdinalDateValid year (day)

namespace Gregorian

/-- The number of days in a given month according to the proleptic Gregorian calendar. -/
def monthLength (year: Int) (month : Int) : Int :=
  let month' := clip' 1 12 month (by simp_arith)
  let month'' : Fin 12 := month'
  ((monthLengths (isLeapYear year)).get month'').2

private def rolloverMonths (ym : Int × Int) : Int × Int  :=
  let (y, m) := ym
  (y + ((m - 1) / 12), ((m - 1) % 12) + 1)

private def addMonths (n : Int) (day : Day) : Int × Int × Int :=
  let ⟨y, m, d, _⟩ := toGregorian day
  let (y', m') := rolloverMonths (y, m + n)
  (y', m', d)

/-- Add months, with days past the last day of the month clipped to the last day.
For instance, 2005-01-30 + 1 month = 2005-02-28. -/
def addMonthsClip (n : Int) (day : Day) : Day :=
  let (y, m, d) := addMonths n day
  fromGregorian y m d

/-- Add months, with days past the last day of the month rolling over to the next month.
For instance, 2005-01-30 + 1 month = 2005-03-02. -/
def addMonthsRollOver (n : Int) (day : Day) : Day :=
  let (y, m, d) := addMonths n day
  Day.addDays (d - 1) (fromGregorian y m 1)

/-- Add years, matching month and day, with Feb 29th clipped to Feb 28th if necessary.
For instance, 2004-02-29 + 2 years = 2006-02-28. -/
def addYearsClip (n : Int) (day : Day) : Day :=
  addMonthsClip (n * 12) day

/-- Add years, matching month and day, with Feb 29th rolled over to Mar 1st if necessary.
-- For instance, 2004-02-29 + 2 years = 2006-03-01. -/
def addYearsRollOver (n : Int) (day : Day) := addMonthsRollOver (n * 12) day

/-- Add months (clipped to last day), then add days -/
def addDurationClip (cd : CalendarDiffDays) (day : Day) :=
  Day.addDays cd.days <| addMonthsClip cd.months day

/-- Add months (rolling over to next month), then add days -/
def addDurationRollOver (cd : CalendarDiffDays) (day : Day) :=
  Day.addDays cd.days <| addMonthsRollOver cd.months day

/-- Calendrical difference, with as many whole months as possible -/
def diffDurationClip (day2 : Day) (day1 : Day) : CalendarDiffDays :=
    let ⟨y1, m1, d1, _⟩  := toGregorian day1
    let ⟨y2, m2, d2, _⟩   := toGregorian day2
    let ym1 := y1 * 12 + m1
    let ym2 := y2 * 12 + m2
    let ymdiff := ym2 - ym1
    let ymAllowed :=
        if day2 >= day1
            then
                if d2 >= d1
                    then ymdiff
                    else ymdiff - 1
            else
                if d2 <= d1
                    then ymdiff
                    else ymdiff + 1
    let dayAllowed := addDurationClip ⟨ymAllowed, 0⟩ day1
    ⟨ymAllowed, Day.diffDays day2 dayAllowed⟩

private partial def findpos (day2 : Day) (day1 : Day) (mdiff : Int) : CalendarDiffDays :=
  let dayAllowed := addDurationRollOver ⟨mdiff, 0⟩  day1
  let dd := Day.diffDays day2 dayAllowed
  if dd >= 0 then ⟨mdiff, dd⟩  else findpos day2 day1 (mdiff - 1)

/-- Calendrical difference, with as many whole months as possible. -/
def diffDurationRollOver (day2 : Day) (day1 : Day) : CalendarDiffDays :=
    let ⟨y1, m1, _, _⟩  := toGregorian day1
    let ⟨y2, m2, _, _⟩  := toGregorian day2
    let ym1 := y1 * 12 + m1
    let ym2 := y2 * 12 + m2
    let ymdiff := ym2 - ym1
    let findneg (mdiff : Int) : CalendarDiffDays :=
        let dayAllowed := addDurationRollOver ⟨mdiff, 0⟩ day1
        let dd := Day.diffDays day2 dayAllowed
        if dd <= 0 then ⟨mdiff, dd⟩  else findpos day2 day1 (mdiff + 1)
    if day2 >= day1
        then findpos day2 day1 ymdiff
        else findneg ymdiff

end Gregorian
