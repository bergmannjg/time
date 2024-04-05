import Time.ZeroPad
import Time.LocalTime.LocalTime
import Time.LocalTime.TimeZone
import Time.LocalTime.TimeOfDay
import Time.LocalTime.ZonedTime
import Time.Calendar.OrdinalDate
import Time.Calendar.Gregorian

namespace Time

class ToISO8601 (α : Type u) where
  toISO8601 : α → String

export ToISO8601 (toISO8601)

instance : ToISO8601 Date where
  toISO8601 a := s!"{toZeroPadded a.Year 4}-{toZeroPadded a.Month 2}-{toZeroPadded a.Day 2}"

instance : ToISO8601 TimeOfDay where
  toISO8601 a :=
    let second := s!"{toZeroPadded a.Second.val.numerator 2}{Fixed.denominatorToString a.Second.val}"
    s!"{toZeroPadded a.Hour.val 2}:{toZeroPadded a.Minute.val 2}:{second}"

instance : ToISO8601 LocalTime where
  toISO8601 a := s!"{toISO8601 <| toGregorian a.localDay}T{toISO8601 a.localTimeOfDay}"

instance : ToISO8601 ZonedTime where
  toISO8601 a :=
    let prefixStr := if a.timeZone.timeZoneMinutes >= 0 then "+" else "-"
    let toTzOffsetString :=
      s!"{prefixStr}{(toZeroPadded (a.timeZone.timeZoneMinutes / 60) 2) ++ ":00"}"
    s!"{toISO8601 a.localTime}{toTzOffsetString}"
