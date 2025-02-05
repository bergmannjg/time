import Time.Verify.Calendar.OrdinalDate
import Time.Verify.Calendar.Gregorian

/-!
# Verification

The date transformations and calculations are verified relative to a intuitive specification
of [next_date](https://bergmannjg.github.io/time/Time/Verify/Calendar/Gregorian.html#Verify.Gregorian.next_date).

It is proved that the following diagrams commute:

| [GregorianDate](https://bergmannjg.github.io/time/Time/Calendar/MonthDay.html#Time.Date) | Transformation | [OrdinaleDate](https://bergmannjg.github.io/time/Time/Calendar/OrdinalDate.html#Time.OrdinalDate) |Transformation | [Modified Julian Day](https://bergmannjg.github.io/time/Time/Calendar/Days.html#Time.Day) |
|:---------------:|:--------:|:------:|:------:|:------:|
|&nbsp;|&nbsp;|&nbsp;|&nbsp;|&nbsp;|
| dt | => dateToOrdinalDate => | odt | => fromOrdinalDate => | mjd |
| &#8659; next_date | [proof](https://bergmannjg.github.io/time/Time/Verify/Calendar/Gregorian.html#Verify.Gregorian.next_date_eq_next_date)  | &#8659; next_date | [proof](https://bergmannjg.github.io/time/Time/Verify/Calendar/OrdinalDate.html#Verify.OrdinalDate.next_date_eq_mjd_add_one) | &#8659; add 1 |
| dt | <= ordinalDateToDate <= | odt | <= toOrdinalDate <= | mjd |

-/
