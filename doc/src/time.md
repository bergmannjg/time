# Time library

Time, clocks and calendars. Port of the [haskell time library](https://github.com/haskell/time)
to Lean 4.

## SystemTime

[SystemTime](../Time/Clock/SystemTime.html) is time returned by system clock functions.
It has a precision of one nanosecond.

```lean
structure SystemTime where
  sec  : Int
  nsec : UInt32
```

```lean
-- ⊢ IO IO.FS.SystemTime
#eval getSystemTime
-- { sec := 1680959011, nsec := 928622514 }
```

## DiffTime

[DiffTime](../Time/Clock/DiffTime.html#Time.DiffTime) is a length of time,
as measured by a clock. It has a precision of one nanosecond ([Fixed 9](../Time/Fixed.html#Time.Fixed)).

```lean
structure Fixed (precision : Nat) where
  val : Int

structure DiffTime where
  val : Fixed 9
```

```lean
-- ⊢ ℤ → ℕ → DiffTime
#eval DiffTime.fromSecNsec 1680959011 928622514
-- { val := { val := 1680959011928622514 } }
```

## UTCTime

[UTCTime](../Time/Clock/UTCTime.html#Time.UTCTime) is a representation of UTC.
It consists of the day number, and a time offset from midnight.

```lean
structure UTCTime where
  utctDay : Day
  utctDayTime : DiffTime
```

```lean
-- ⊢ IO.FS.SystemTime → UTCTime
#eval UTCTime.toUTCTime { sec := 1680959011, nsec := 928622514 }
-- { utctDay := { modifiedJulianDay := 60042 },
--   utctDayTime := { val := { val := 47011928622514  } } }
```

## Day

The [Day](../Time/Calendar/Days.html#Time.Day) data type is an abstract way of referring to a
calendar date. The toGregorian and
fromGregorian functions will construct and deconstruct a Day from the usual year-month-day format.

```lean
structure Day where
  modifiedJulianDay : Int
```

```lean
-- ⊢ ℤ → ℤ → ℤ → Day
#eval fromGregorian 2023 2 12
-- { modifiedJulianDay := 59987 }
```

## Date

The [Date](../Time/Calendar/Gregorian.html#Time.Date) is a calendar date in the proleptic Gregorian calendar.

```lean
structure Date where
  Year : Int
  Month : Set.Icc 1 12
  Day : Set.Icc 1 31
```

```lean
-- ⊢ Day → Date
#eval toGregorian { modifiedJulianDay := 59987 }
-- { Year := 2023, Month := 2, Day := 12 }
```

## TimeOfDay

[TimeOfDay](../Time/LocalTime/TimeOfDay.html#Time.TimeOfDay) consists of an hour
of the day, a minute of the hour, and a second of the minute, including fractions
of a second up to a resolution of one nanosecond.

```lean
structure TimeOfDay where
  Hour : Set.Ico 0 24
  Minute : Set.Ico 0 60
  Second : Set.Ico ⟨0⟩ ⟨60000000000⟩
```

```lean
-- ⊢ DiffTime → TimeOfDay
#eval TimeOfDay.timeToTimeOfDay { val := { val := 47011928622514  } }
-- { Hour := 13, Minute := 3, Second := { val := 31928622514 } }
```

## TimeZone

A [TimeZone](../Time/LocalTime/TimeZone.html#Time.TimeZone) represents an offset
from UTC measured in minutes.

```lean
structure TimeZone where
  timeZoneMinutes : Int
  timeZoneSummerOnly : Bool
  timeZoneName : String
```

```lean
-- ⊢ IO TimeZone
#eval TimeZone.getTimeZone
-- { timeZoneMinutes := 120, timeZoneSummerOnly := true, timeZoneName := "CEST" }
```

## LocalTime

A Day with a TimeOfDay forms a [LocalTime](../Time/LocalTime/LocalTime.html#Time.LocalTime).

```lean
structure LocalTime where
  localDay : Day
  localTimeOfDay : TimeOfDay
```

```lean
-- ⊢ TimeZone → UTCTime → LocalTime
#eval LocalTime.utcToLocalTime
  { timeZoneMinutes := 120, timeZoneSummerOnly := true, timeZoneName := "CEST" }
  { utctDay := { modifiedJulianDay := 60042 },
    utctDayTime := { val := { val := 47011928622514  } } }
-- { localDay := { modifiedJulianDay := 60042 },
--   localTimeOfDay := { Hour := 15, Minute := 3, Second := { val := 31928622514 } } }
```

## ZonedTime

A [ZonedTime](../Time/LocalTime/ZonedTime.html#Time.ZonedTime) is a LocalTime
together with a TimeZone.

```lean
structure ZonedTime where
  localTime : LocalTime
  timeZone : TimeZone
```

```lean
-- ⊢ LocalTime → TimeZone → ZonedTime
#eval ZonedTime.mk
  { localDay := { modifiedJulianDay := 60042 },
    localTimeOfDay := { Hour := ⟨15, (by simp)⟩, Minute := ⟨3, (by simp)⟩,
                        Second := ⟨⟨31928622514⟩, (by simp)⟩ } }
  { timeZoneMinutes := 120, timeZoneSummerOnly := true, timeZoneName := "CEST" }
-- { localTime :=
--      { localDay := { modifiedJulianDay := 60042 },
--        localTimeOfDay := { Hour := 15, Minute := 3, Second := { val := 31928622514 } } },
--   timeZone := { timeZoneMinutes := 120, timeZoneSummerOnly := true, timeZoneName := "CEST" } }
```

## Parse

[Parse](../Time/Format/Parse.html#Time.parse) a time value (i.e. instance of
[Time.ParseTime](../Time/Format/Parse/Class.html#Time.ParseTime))
given a [format](../Time/Specifier.html) string.

```lean
#eval (parse .defaultTimeLocale "%Y-%m-%dT%H:%M:%S" "2023-02-12T12:24:30"
        : Option LocalTime)
-- some
--   { localDay := { modifiedJulianDay := 59987 },
--     localTimeOfDay := { Hour := 12, Minute := 24,
--                         Second := { val := 30000000000 } } }
```

## Format

Format a time value (i.e. instance of
[Time.ToISO8601](..//Time/Format.html#Time.ToISO8601)) to ISO8601.

```lean
#eval toISO8601 (default : ZonedTime)
-- "1858-11-17T00:00:00+00:00"
```
