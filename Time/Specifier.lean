import Time.Format.Locale

namespace Time

/-!

# Parse and Format Specifier

The general form is `%&lt;modifier>&lt;width><alternate>&lt;specifier>`, where `&lt;modifier>`, `&lt;width>`, and `&lt;alternate>` are optional.

### modifier

glibc-style modifiers can be used before the specifier (here marked as `z`):

* `%-z` no padding

* `%_z` pad with spaces

* `%0z` pad with zeros

* `%^z` convert to upper case

* `%#z` convert to lower case (consistently, unlike glibc)

### width

Width digits can also be used after any modifiers and before the specifier (here marked as `z`), for example:

* `%4z` pad to 4 characters (with default padding character)

* `%_12z` pad with spaces to 12 characters

### alternate

An optional `E` character indicates an alternate formatting. Currently this only affects `%Z` and `%z`.

* `%Ez` alternate formatting

### specifier

* `%%` `%`
* `%t` tab
* `%n` newline

* [Specifier](#Time.Specifier)
* [SubstituteSpecifier](#Time.SubstituteSpecifier)

-/

inductive Specifier
  /-- timezone offset in the format `±HHMM` -/
  | z
  /-- timezone offset in the format `±HH: MM` -/
  | Ez
  /-- timezone name (or else offset in the format `±HHMM`) -/
  | Z
  /-- timezone name (or else offset in the format `±HH: MM`) -/
  | EZ
  /-- day-half of day from (`amPm` `locale`), converted to lowercase, `am`, `pm` -/
  | P
  /-- day-half of day from (`amPm` `locale`), `AM`, `PM` -/
  | p
  /-- hour of day (24-hour), 0-padded to two chars, `00` - `23` -/
  | H
  /-- hour of day (24-hour), space-padded to two chars, ` 0` - `23` -/
  | k
  /-- hour of day-half (12-hour), 0-padded to two chars, `01` - `12` -/
  | I
  /-- hour of day-half (12-hour), space-padded to two chars, ` 1` - `12` -/
  | l
  /-- minute of hour, 0-padded to two chars, `00` - `59` -/
  | M
  /-- second of minute (without decimal part), 0-padded to two chars, `00` - `60` -/
  | S
  /-- picosecond of second, 0-padded to twelve chars, `000000000000` - `999999999999`. -/
  | q
  /-- decimal point and fraction of second, up to 12 second decimals, without trailing zeros.
      For a whole number of seconds, `%Q` omits the decimal point unless padding is specified. -/
  | Q
  /-- day of week number for Week Date format, `1` (= Monday) - `7` (= Sunday) -/
  | u
  /-- day of week number, `0` (= Sunday) - `6` (= Saturday) -/
  | w
  /-- day of week, short form (`snd` from `Time.TimeLocale.wDays` `locale`), `Sun` - `Sat` -/
  | a
  /-- day of week, long form (`fst` from `Time.TimeLocale.wDays` `locale`), `Sunday` - `Saturday` -/
  | A
  /-- year, no padding. Note `%0Y` and `%_Y` pad to four chars -/
  | Y
  /-- year, no padding. Note `%0Y` and `%_Y` pad to four chars -/
  | G
  /-- year of century, 0-padded to two chars, `00` - `99` -/
  | y
  /-- year of century, 0-padded to two chars, `00` - `99` -/
  | g
  /-- century, no padding. Note `%0C` and `%_C` pad to two chars -/
  | C
  /-- month name, long form (`fst` from `Time.TimeLocale.months` `locale`), `January` - `December` -/
  | B
  /-- month name, short form (`snd` from `Time.TimeLocale.months` `locale`), `Jan` - `Dec` -/
  | b
  /--  month of year, 0-padded to two chars, `01` - `12` -/
  | m
  /-- day of month, 0-padded to two chars, `01` - `31` -/
  | d
  /-- day of month, space-padded to two chars,  ` 1` - `31` -/
  | e
  /-- day of year, 0-padded to three chars, `001` - `366` -/
  | j
  /-- century for Week Date format, no padding. Note `%0f` and `%_f` pad to two chars -/
  | f
  /-- week of year for Week Date format, 0-padded to two chars, `01` - `53` -/
  | V
  /-- week of year where weeks start on Sunday (as `sundayStartWeek`), 0-padded to two chars, `00` - `53` -/
  | U
  /-- week of year where weeks start on Monday (as `mondayStartWeek`), 0-padded to two chars, `00` - `53` -/
  | W
  deriving Repr, BEq

inductive SubstituteSpecifier
  /-- as 'dateTimeFmt' of  `Time.TimeLocale` -/
  | c
  /-- same as `%H:%M` -/
  | R
  /-- same as `%H:%M:%S` -/
  | T
  /-- as `timeFmt` of `Time.TimeLocale` (e.g. `%H:%M:%S`) -/
  | X
  /-- as `time12Fmt` of `Time.TimeLocale` (e.g. `%I:%M:%S %p`) -/
  | r
  /-- same as `%m\/%d\/%y` -/
  | D
  /-- same as `%Y-%m-%d` -/
  | F
  /--  as `dateFmt` of `Time.TimeLocale` (e.g. `%m\/%d\/%y`) -/
  | x
  /--  month name, short form -/
  | h

def toSpecifier : Char -> Option Specifier
  -- century
  | 'C' => some Specifier.C
  | 'f' => some Specifier.f
  -- year
  | 'Y' => some Specifier.Y
  | 'G' => some Specifier.G
  -- year of century
  | 'y' => some Specifier.y
  | 'g' => some Specifier.g
  -- month of year
  | 'B' => some Specifier.B
  | 'b' => some Specifier.b
  | 'm' => some Specifier.m
  -- day of month
  | 'd' => some Specifier.d
  | 'e' => some Specifier.e
  -- week of year
  | 'V' => some Specifier.V
  | 'U' => some Specifier.U
  | 'W' => some Specifier.W
  -- day of week
  | 'u' => some Specifier.u
  | 'A' => some Specifier.A
  | 'a' => some Specifier.a
  | 'w' => some Specifier.w
  -- day of year
  | 'j' => some Specifier.j
  -- hour of day (i.e. 24h)
  | 'H' => some Specifier.H
  -- minute of hour
  | 'M' => some Specifier.M
  -- second of minute
  | 'S' => some Specifier.S
  -- nanosecond of second
  | 'q' => some Specifier.q
  | 'Q' => some Specifier.Q
  -- time zone
  | 'z' => some Specifier.z
  | _ => none

def toSubstituteSpecifier : Char -> Option SubstituteSpecifier
  | 'c' => some SubstituteSpecifier.c
  | 'R' => some SubstituteSpecifier.R
  | 'T' => some SubstituteSpecifier.T
  | 'X' => some SubstituteSpecifier.X
  | 'r' => some SubstituteSpecifier.r
  | 'D' => some SubstituteSpecifier.D
  | 'F' => some SubstituteSpecifier.F
  | 'x' => some SubstituteSpecifier.x
  | 'h' => some SubstituteSpecifier.h
  | _ => none
