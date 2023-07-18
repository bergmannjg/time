import Mathlib.Tactic.NormNum
import Mathlib.Init.Algebra.Order
import Std.Data.Nat.Lemmas
import Std.Data.Int.Lemmas
import Time.Calendar.Days
import Time.Calendar.Private

namespace Time

inductive DayOfYear where
  | common : Set.Icc 1 365 -> DayOfYear
  | leap : Set.Icc 1 366 -> DayOfYear
  deriving Repr, BEq

instance : Coe DayOfYear (Set.Icc 1 366) where
  coe
    | .common d => ⟨d.val, And.intro (d.property.left) (Nat.le_step d.property.right)⟩
    | .leap d => d

/-- ISO 8601 Ordinal Date  -/
structure OrdinalDate where
  year : Int
  dayOfYear : DayOfYear
  deriving Repr, BEq

def dayOfYear (dayOfYear: DayOfYear) : Nat :=
  match dayOfYear with
  | .common d => d.val
  | .leap d => d.val

/-- Is this year a leap year according to the proleptic Gregorian calendar? -/
def isLeapYear (year : Int) :=
  (Int.mod year 4 == 0) && ((Int.mod year 400 == 0) || not (Int.mod year 100 == 0))

def toDayOfYear (year: Int) (d': Int) (hd1 : 0 ≤ d') (hd2 : d' < 3*365 + 366) : DayOfYear :=
  if h : d' / 365 ≤ 3
  then
    let yd' := d' % 365 + 1
    let yd := Int.toNat yd'

    have h1 : 0 < yd := by
      have ha : 0 <= d' % 365 := by simp [Int.emod_nonneg _]
      have hb : 0 < yd' := Int.lt_add_one_iff.mpr ha
      exact ((Int.toNat_lt_toNat hb).mpr hb)

    have h2 : yd <= 365 := by
      have ha : d' % 365 < 365 := by simp [Int.emod_lt_of_pos _]
      have hb : yd' <= 365 := by simp [Int.add_one_le_iff.mpr ha]
      exact Int.toNat_le_toNat hb

    if isLeapYear year
    then .leap ⟨yd, And.intro h1 (Nat.le_step h2)⟩
    else .common ⟨yd, And.intro h1 h2⟩
  else
    let yd' := d' - 3*365 + 1
    let yd := Int.toNat yd'

    have h1 : 0 < yd := by
      have ha : 3*365 < d' / 365  * 365 := by simp [not_le.mp h]
      have hb : d' / 365 * 365 ≤ d' := by simp [Int.ediv_mul_le _]
      have hc : 3*365 < d' := Int.le_trans ha hb
      have hd : 0 < yd' := Int.add_pos (Int.sub_pos_of_lt hc) (by simp)
      exact ((Int.toNat_lt_toNat hd).mpr hd)

    have h2 : yd ≤ 366 := by
      have ha : d' - 3*365 < 366 := Int.sub_right_lt_of_lt_add hd2
      exact Int.toNat_le_toNat (Int.add_one_le_of_lt ha)

    .leap ⟨yd, And.intro h1 h2⟩

/-- from modified Julian day to year and day of year -/
def toOrdinalDate (mjd : Day) : OrdinalDate :=
  let a := mjd.modifiedJulianDay - (default : Day).modifiedJulianDay
  /- there are 146097 days in 400 years (4*36524 + 1) -/
  let quadcent := a / 146097
  let b := a % 146097
  /- there are 36524 days in 100 years if not including a year divisible by 400 (76*365+24*366) -/
  let cent := min (b / 36524) 3
  let c := b - (cent * 36524)
  /- there are 1461 days in 4 years including a leap year (3*365 + 366) -/
  let quad := c / 1461
  let d' := c % 1461

  have h1 : 0 <= d' := by simp [Int.emod_nonneg _]
  have h2 : d' < 3*365 + 366 := by
    have ha : d' < 1461 := by simp [Int.emod_lt_of_pos _]
    exact ha

  let y := min (d' / 365) 3
  let year := quadcent * 400 + cent * 100 + quad * 4 + y + 1

  let yd := toDayOfYear year d' h1 h2

  ⟨year, yd⟩

theorem ite_ge {α : Type} (f : α → Bool) (v : α) (a b c : Nat) (h₁ : c <= a) (h₂ : c <= b):
    c <= if (f v) then a else b := by
  match f v with
  | true => exact h₁
  | false => exact h₂

private inductive YearBase where
  | Zero
  | One
  deriving Repr, BEq

private def clipDayOfYear (b : YearBase) (year : Int) (dayOfYear : Int) : Nat :=
  match b with
  | .Zero => Private.clip 0 (if isLeapYear year then 365 else 364) dayOfYear
              (ite_ge _ _ _ _ 0 (by norm_num1) (by norm_num1))
  | .One => Private.clip 1 (if isLeapYear year then 366 else 365) dayOfYear
              (ite_ge _ _ _ _ 1 (by norm_num1) (by norm_num1))

private def clipDayOfYearValid (b : YearBase) (year : Int) (dayOfYear : Int) : Option Nat :=
  match b with
  | .Zero => Private.clipValid 0 (if isLeapYear year then 365 else 364) dayOfYear
              (ite_ge _ _ _ _ 0 (by norm_num1) (by norm_num1))
  | .One => Private.clipValid 1 (if isLeapYear year then 366 else 365) dayOfYear
              (ite_ge _ _ _ _ 1 (by norm_num1) (by norm_num1))

private def toModifiedJulianDay (year : Int) (dayOfYear : Nat) : Int :=
  /- Gregorian serial date minus difference to modified julian date. -/
  let y := year - 1
  dayOfYear + (365 * y) + ( y / 4) - (y / 100) + ( y / 400)
    + ((default : Day).modifiedJulianDay -  1)

def firstDayOfYear (year : Int) : DayOfYear :=
    if isLeapYear year then .leap ⟨1, (by simp)⟩ else .common ⟨1, (by simp)⟩

/--  Convert from ISO 8601 Ordinal Date format.
Invalid day numbers will be clipped to the correct range (1 to 365 or 366). -/
def fromOrdinalDayOfYear (year : Int) (d : Set.Icc 1 366) : Day :=
  let day' := clipDayOfYear .One year d.val
  { modifiedJulianDay := toModifiedJulianDay year day' }

/--  Convert from ISO 8601 Ordinal Date format.
Invalid day numbers will be clipped to the correct range (1 to 365 or 366). -/
def fromOrdinalDate (dt : OrdinalDate) : Day :=
  fromOrdinalDayOfYear dt.year dt.dayOfYear

/--  Convert from ISO 8601 Ordinal Date format. -/
def fromOrdinalDateValid (year : Int) (day : Int) : Option Day := do
  let day' ← clipDayOfYearValid .One year day
  return { modifiedJulianDay := toModifiedJulianDay year day' }

/-- The inverse of 'mondayStartWeek'. Get a 'Day' given the year,
the number of the Monday-starting week, and the day of the week.
The first Monday is the first day of week 1, any earlier days in the year
are week 0 (as @%W@ in 'Data.Time.Format.formatTime'). -/
def fromMondayStartWeekValid (year : Int) (w : Int) (d : Int) : Option Day := do
  let d' ←  Private.clipValid 1 7 d (by norm_num1)
  -- first day of the year
  let firstDay := fromOrdinalDate ⟨year, firstDayOfYear year⟩
  -- 0-based week of year
  let zbFirstMonday := (5 - firstDay.modifiedJulianDay) % 7
  -- 0-based week number
  let zbWeek := w - 1
  -- 0-based day of week
  let zbDay := d' - 1
  -- 0-based day in year
  let zbYearDay := zbFirstMonday + 7 * zbWeek + zbDay
  let zbYearDay' ← clipDayOfYearValid .Zero year zbYearDay
  return Day.addDays zbYearDay' firstDay

/-- The inverse of 'sundayStartWeek'. Get a 'Day' given the year and
the number of the day of a Sunday-starting week.
The first Sunday is the first day of week 1, any earlier days in the
year are week 0 (as @%U@ in 'Data.Time.Format.formatTime'). -/
def fromSundayStartWeekValid (year : Int) (w : Int) (d : Int) : Option Day := do
  let d' ←  Private.clipValid 0 6 d (by norm_num1)
  -- first day of the year
  let firstDay := fromOrdinalDate ⟨year, firstDayOfYear year⟩
  -- 0-based week of year
  let zbFirstSunday := (4 - firstDay.modifiedJulianDay) % 7
  -- 0-based week number
  let zbWeek := w - 1
  -- 0-based day of week
  let zbDay := d'
  -- 0-based day in year
  let zbYearDay := zbFirstSunday + 7 * zbWeek + zbDay
  let zbYearDay' ← clipDayOfYearValid .Zero year zbYearDay
  return Day.addDays zbYearDay' firstDay
