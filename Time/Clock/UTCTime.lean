import Time.Calendar.Days
import Time.Calendar.OrdinalDate
import Time.Clock.DiffTime

namespace Time

/-- This is a representation of UTC.
It consists of the day number, and a time offset from midnight.
-/
structure UTCTime where
  utctDay : Day
  utctDayTime : DiffTime
  deriving Repr, BEq

namespace UTCTime

instance : ToString UTCTime where
  toString a := s!"{a.utctDay.modifiedJulianDay}, {a.utctDayTime}"

/-- unix epoch day as modified julian day -/
def systemEpochDay := 40587

/-- seconds of day -/
def nominalDay := 86400 -- secs of day

def toUTCTime (now : {t : IO.FS.SystemTime // t.nsec.toNat < 10 ^ 9}) : UTCTime :=
  let (ndays, secsOfDay) := ((now.val.sec / nominalDay) + systemEpochDay, now.val.sec % nominalDay)
  ⟨⟨ndays⟩, DiffTime.fromSecNsec Sign.Nonneg secsOfDay.toNat now.val.nsec.toNat now.property⟩

def toDiffTime (utc : UTCTime) : DiffTime :=
  DiffTime.fromSec (utc.utctDay.modifiedJulianDay * nominalDay) + utc.utctDayTime

def sub (utc1 : UTCTime) (utc2 : UTCTime) : DiffTime :=
  (toDiffTime utc1) - (toDiffTime utc2)

instance : HSub UTCTime UTCTime DiffTime where
  hSub := sub

end UTCTime
