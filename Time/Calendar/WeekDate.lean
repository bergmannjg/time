import Time.Calendar.Clip
import Time.Calendar.Days
import Time.Calendar.OrdinalDate
import Time.Calendar.Week
import Std

namespace Time

open Clip

/-- FirstWeekType

  * `FirstWholeWeek` - first week is the first whole week of the year
  * `FirstMostWeek` - first week is the first week with four days in the year
-/
inductive FirstWeekType
  |  FirstWholeWeek
  |  FirstMostWeek
  deriving Repr, BEq

/-- The number of days from b to the next a. -/
def dayOfWeekDiff (a : DayOfWeek) (b : DayOfWeek) : Int :=
  Int.emod (DayOfWeek.fromDayOfWeek a - DayOfWeek.fromDayOfWeek b) 7

/-- `dayOfWeekDiff a b = a - b` in range 0 to 6. -/
theorem dayOfWeekDiff_range (a b : DayOfWeek) : 0 <= dayOfWeekDiff a b ∧ dayOfWeekDiff a b <= 6
 := by cases a <;> cases b <;> simp_arith

/-- The first day-of-week on or after some day -/
def firstDayOfWeekOnAfter (dw : DayOfWeek) (d : Day) : Day :=
  Day.addDays (dayOfWeekDiff dw <| DayOfWeek.dayOfWeek d) d

def firstDayOfWeekCalendar (wt : FirstWeekType) (dow : DayOfWeek) (year : Int) : Day :=
  let jan1st := fromOrdinalDate (firstDayOfYearDate year)
  match wt with
  | .FirstWholeWeek => firstDayOfWeekOnAfter dow jan1st
  | .FirstMostWeek => firstDayOfWeekOnAfter dow <| Day.addDays (-3) jan1st

private def getday (wy : Int) (d1 : Day) (ws : DayOfWeek) (dw : DayOfWeek) : Day :=
  Day.addDays (((wy - 1) * 7) + (dayOfWeekDiff dw ws)) d1

/-- Convert to the given kind of "week calendar".
Note that the year number matches the weeks, and so is not always the same
as the Gregorian year number. -/
def toWeekCalendar (wt : FirstWeekType) (ws : DayOfWeek) (d : Day) : Int × Int × DayOfWeek :=
  let dw := DayOfWeek.dayOfWeek d
  let ⟨y0, _, _⟩ := toOrdinalDate d
  let j1p := firstDayOfWeekCalendar wt ws $ Nat.pred y0.toNat
  let j1 := firstDayOfWeekCalendar wt ws y0
  let j1s := firstDayOfWeekCalendar wt ws $ Nat.succ y0.toNat
  if d < j1 then (y0-1, 1 + (Int.div (Day.diffDays d j1p) 7), dw)
  else if d < j1s then (y0, 1 + (Int.div (Day.diffDays d j1) 7), dw)
  else (1 + y0, 1 + (Int.div (Day.diffDays d j1s) 7), dw)

/-- Convert from the given kind of "week calendar". `ws` is the first day of each week.
Invalid week and day values will be clipped to the correct range. -/
def fromWeekCalendar (wt : FirstWeekType) (ws : DayOfWeek) (y : Int) (wy : Int) (dw : DayOfWeek)
   : Day :=
  let d1 := firstDayOfWeekCalendar wt ws y
  let wy' := clip 1 53 wy (by omega)
  let d1s := firstDayOfWeekCalendar wt ws (y + 1)
  let day := getday wy' d1 ws dw
  if wy' == 53 then if day >= d1s then getday 52 d1 ws dw else day else day

def fromWeekCalendarValid (wt : FirstWeekType) (ws : DayOfWeek) (y : Int) (wy : Int)
    (dw : DayOfWeek) : Option Day :=
  let d := fromWeekCalendar wt ws y wy dw
  if toWeekCalendar wt ws d == (y, wy, dw) then some d else none

/-- Convert from ISO 8601 Week Date format.
* First argument is year,
* second week number (1-52 or 53),
* third day of week (1 for Monday to 7 for Sunday).

Invalid week and day values will be clipped to the correct range. -/
def fromWeekDate (y : Int) (wy : Int) (dw : Int) : Day :=
  fromWeekCalendar .FirstMostWeek .Monday y wy (DayOfWeek.toDayOfWeek dw.toNat)

/-- Convert from ISO 8601 Week Date format.
* First argument is year,
* second week number (1-52 or 53),
* third day of week (1 for Monday to 7 for Sunday).

Invalid week and day values will be clipped to the correct range. -/
def fromWeekDateValid (y : Int) (wy : Int) (dwr : Int) : Option Day := do
  let dw ← clip? 1 7 dwr (by omega)
  fromWeekCalendarValid .FirstMostWeek .Monday y wy (DayOfWeek.toDayOfWeek dw)
