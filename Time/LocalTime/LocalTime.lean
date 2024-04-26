import Time.Calendar.Days
import Time.Calendar.Gregorian
import Time.Clock.DiffTime
import Time.Clock.UTCTime
import Time.LocalTime.TimeOfDay
import Time.LocalTime.TimeZone

namespace Time

structure LocalTime where
  localDay : Day
  localTimeOfDay : TimeOfDay
  deriving Repr, BEq

namespace Time.Notation

/-- LocalTime syntactic category -/
declare_syntax_cat datetime
/-- LocalTime from numeric literals year, month, day, hour, minute and second -/
syntax num noWs "-" noWs num noWs "-" noWs num ws num noWs ":" noWs num (noWs ":" noWs num)? : datetime
syntax "datetime%" datetime : term

/--
  `datetime% year-month-day hour:minute:second` is notation for
  `(⟨Time.fromGregorianDate (Time.Date.mk year ⟨month, by omega⟩ ⟨day, by omega⟩ (by native_decide)),
    Time.TimeOfDay.mk ⟨hour, by omega⟩ ⟨minute, by omega⟩ (Time.TimeOfDay.toSecond second 0 (by omega) (by omega))⟩
    : Time.LocalTime)`
  for the numeric literals year, month, day, hour, minute and second.
-/
macro_rules
| `(datetime% $y:num-$mo:num-$d:num $h:num:$mi:num$[:$s:num]?) =>
    `((⟨Time.fromGregorianDate (Time.Date.mk $y ⟨$mo, by omega⟩ ⟨$d, by omega⟩ (by native_decide)),
      Time.TimeOfDay.mk ⟨$h, by omega⟩ ⟨$mi, by omega⟩
        (Time.TimeOfDay.toSecond $(s.getD (Lean.Quote.quote 0)) 0 (by omega) (by omega))⟩
      : Time.LocalTime))

end Time.Notation

instance : ToString LocalTime where
  toString a := s!"{a.localDay}, {a.localTimeOfDay}"

instance : Inhabited LocalTime where
  default := ⟨default, default⟩

namespace LocalTime

def addDays (n : Int) (lt : LocalTime) : LocalTime :=
  ⟨Day.addDays n lt.localDay, lt.localTimeOfDay⟩

def utcToLocalTime (tz : TimeZone) (utc : UTCTime) : LocalTime :=
  let (n, tod) := TimeOfDay.utcToLocalTimeOfDay tz (TimeOfDay.timeToTimeOfDay utc.utctDayTime)
  ⟨Day.addDays n utc.utctDay, tod⟩

def localTimeToUTCTime (tz : TimeZone) (localTime : LocalTime) : UTCTime :=
  let (n, tod) := TimeOfDay.localToUTCTimeOfDay tz localTime.localTimeOfDay
  ⟨Day.addDays n localTime.localDay, TimeOfDay.timeOfDayToTime tod⟩
