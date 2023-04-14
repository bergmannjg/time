import Time.Calendar.Days
import Time.Clock.DiffTime
import Time.Clock.UTCTime
import Time.LocalTime.TimeOfDay
import Time.LocalTime.TimeZone

namespace Time

structure LocalTime where
  localDay : Day
  localTimeOfDay : TimeOfDay
  deriving Repr, BEq

instance : ToString LocalTime where
  toString a := s!"{a.localDay}, {a.localTimeOfDay}"

instance : Inhabited LocalTime where
  default := ⟨⟨0⟩, default⟩

namespace LocalTime

def addDays (n : Int) (lt : LocalTime) : LocalTime :=
  ⟨Day.addDays n lt.localDay, lt.localTimeOfDay⟩

def utcToLocalTime (tz : TimeZone) (utc : UTCTime) : LocalTime :=
  let (n, tod) := TimeOfDay.utcToLocalTimeOfDay tz (TimeOfDay.timeToTimeOfDay utc.utctDayTime)
  ⟨Day.addDays n utc.utctDay, tod⟩

def localTimeToUTCTime (tz : TimeZone) (localTime : LocalTime) : UTCTime :=
  let (n, tod) := TimeOfDay.localToUTCTimeOfDay tz localTime.localTimeOfDay
  ⟨Day.addDays n localTime.localDay, TimeOfDay.timeOfDayToTime tod⟩
