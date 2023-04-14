import Time.Clock.SystemTime
import Time.Clock.DiffTime
import Time.LocalTime.LocalTime
import Time.LocalTime.TimeZone
import Time.LocalTime.TimeOfDay
import Time.Calendar.OrdinalDate
import Time.Calendar.Gregorian

namespace Time

structure ZonedTime where
  localTime : LocalTime
  timeZone : TimeZone
  deriving Repr, BEq

instance : ToString ZonedTime where
  toString a := s!"{a.localTime}, {a.timeZone}"

namespace ZonedTime

def getZonedTime : IO ZonedTime := do
  let utc :=  UTCTime.toUTCTime (← getSystemTime)
  let zone <- TimeZone.getTimeZone
  return ⟨LocalTime.utcToLocalTime zone utc, zone⟩

def sub (lt1 : ZonedTime) (lt2 : ZonedTime) : DiffTime :=
  (LocalTime.localTimeToUTCTime lt1.timeZone lt1.localTime) - (LocalTime.localTimeToUTCTime lt2.timeZone lt2.localTime)

instance : HSub ZonedTime ZonedTime DiffTime where
  hSub := sub

instance : Inhabited ZonedTime where
  default := ⟨⟨⟨0⟩, default⟩, ⟨0, false, ""⟩⟩
