# Time package

Port of the [haskell time library](https://github.com/haskell/time) to [Lean 4](https://github.com/leanprover/lean4) (WIP).

Missing modules

* [FormatTime](https://github.com/haskell/time/blob/master/lib/Data/Time/Format/Format/Class.hs)
* [AbsoluteTime](https://github.com/haskell/time/blob/master/lib/Data/Time/Clock/Internal/AbsoluteTime.hs)

## Usage

see [time library doc](https://bergmannjg.github.io/time/book/time.html)

### From Haskell to Lean

Take the function *toOrdinalDate*, which computes the ISO 8601 ordinal date given a modified Julian day.

In Haskell [toOrdinalDate](https://hackage.haskell.org/package/time-1.12.2/docs/Data-Time-Calendar-OrdinalDate.html) has the type

```haskell
type Year = Integer
type DayOfYear = Int
toOrdinalDate :: Day -> (Year, DayOfYear)
```

and computes the year and the day of year.

In Lean [toOrdinalDate](https://bergmannjg.github.io/time/Time/Calendar/OrdinalDate.html#Time.toOrdinalDate) has the type

```lean
inductive DayOfYear where
  | common : Time.Icc 1 365 -> DayOfYear
  | leap : Time.Icc 1 366 -> DayOfYear

structure OrdinalDate where
  year : Int
  dayOfYear : DayOfYear
  isValid : match dayOfYear with
            | .common _ => isLeapYear year = false
            | .leap _ => isLeapYear year = true

def toOrdinalDate : Day → OrdinalDate
```

and computes the year and the day of year and gives a proof that ordinal date is a valid date.

### Verification

The date transformations and calculations are verified relative to a intuitive specification
of [next_date](https://bergmannjg.github.io/time/Time/Verify/Calendar/Gregorian.html#Verify.Gregorian.next_date).

It is proved that the following diagrams commute:

| [GregorianDate](https://bergmannjg.github.io/time/Time/Calendar/MonthDay.html#Time.Date) | Transformation | [OrdinaleDate](https://bergmannjg.github.io/time/Time/Calendar/OrdinalDate.html#Time.OrdinalDate) |Transformation | [Modified Julian Day](https://bergmannjg.github.io/time/Time/Calendar/Days.html#Time.Day) |
|:---------------:|:--------:|:------:|:------:|:------:|
| dt | => dateToOrdinalDate => | odt | => fromOrdinalDate => | mjd |
| &#8659; next_date | [proof](https://bergmannjg.github.io/time/Time/Verify/Calendar/Gregorian.html#Verify.Gregorian.next_date_eq_next_date)  | &#8659; next_date | [proof](https://bergmannjg.github.io/time/Time/Verify/Calendar/OrdinalDate.html#Verify.OrdinalDate.next_date_eq_mjd_add_one) | &#8659; add 1 |
| dt | <= ordinalDateToDate <= | odt | <= toOrdinalDate <= | mjd |


## Build

* update: lake update
* build: lake build
* build docs: lake -R -Kenv=dev update && lake -R -Kenv=dev build Time:docs
