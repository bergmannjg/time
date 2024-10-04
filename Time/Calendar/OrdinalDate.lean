import Batteries.Data.Nat.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Int.DivMod
import Init.Data.Bool
import Time.Calendar.Days
import Time.Calendar.Clip
import Time.Data.Int.Order

namespace Time

inductive DayOfYear where
  | common : Time.Icc 1 365 -> DayOfYear
  | leap : Time.Icc 1 366 -> DayOfYear
  deriving Repr, BEq

instance : BEq DayOfYear where
  beq a b :=
    match a, b with
    | .common a, .common b => a.val = b.val
    | .leap a, .leap b => a.val = b.val
    | _, _ => false

instance : Coe DayOfYear (Time.Icc 1 366) where
  coe
    | .common d => ⟨d.val, And.intro (d.property.left) (Nat.le_step d.property.right)⟩
    | .leap d => d

/-- Is this year a leap year according to the proleptic Gregorian calendar? -/
def isLeapYear (year : Int) :=
  (year % 4 = 0) && (year % 400 = 0 || not (year % 100 = 0))

/-- ISO 8601 Ordinal Date -/
structure OrdinalDate where
  year : Int
  dayOfYear : DayOfYear
  isValid : match dayOfYear with
            | .common _ => isLeapYear year = false
            | .leap _ => isLeapYear year = true
  deriving Repr

instance : BEq OrdinalDate where
  beq a b := a.year == b.year && decide (a.dayOfYear == b.dayOfYear)

def dayOfYear (dayOfYear: DayOfYear) : Nat :=
  match dayOfYear with
  | .common d => d.val
  | .leap d => d.val

private def toDayOfYear (year: Int) (d': Int) : OrdinalDate :=
  let yd' := d' % 365 + 1
  let yd := Int.toNat yd'

  have h1 : 0 < yd := by
    have ha : 0 <= d' % 365 := by simp [Int.emod_nonneg _]
    have hb : 0 < yd' := Int.lt_add_one_iff.mpr ha
    exact Int.toNat_lt_toNat hb (by omega)

  have h2 : yd <= 365 := by
    have ha : d' % 365 < 365 := by simp_arith [Int.emod_lt_of_pos _]
    have hb : yd' <= 365 := by simp [Int.add_one_le_iff.mpr ha]
    exact Int.toNat_le_toNat hb

  if h : isLeapYear year
  then ⟨year, .leap ⟨yd, And.intro h1 (Nat.le_step h2)⟩, (by simp_all)⟩
  else ⟨year, .common ⟨yd, And.intro h1 h2⟩, (by simp_all)⟩

theorem year_emod_4_zero {qc cent q : Int} (year : Int)
  (h: year = qc * 400 + cent * 100 + q * 4 + 4) : year % 4 = 0 := by
  omega

theorem year_emod_400_zero {qc cent q : Int} (year : Int)
  (h1 : year = qc * 400 + cent * 100 + q * 4 + 4) (h2 : q = 24) (h3 : cent = 3)
    : year % 400 = 0 := by
  omega

theorem year_emod_100_non_zero {qc cent q : Int} (year : Int)
  (h1: year = qc * 400 + cent * 100 + q * 4 + 4) (hle : 0 ≤ q) (h2 : q < 24) : year % 100 ≠ 0 := by
  omega

theorem isLeapYear_of_sum {qc cent q : Int} (year : Int)
  (h1: year = qc * 400 + cent * 100 + q * 4 + 4) (hle : 0 ≤ q) (h2 : q ≤ 24)
  (h3 : q = 24 -> cent = 3) : isLeapYear year := by
  unfold isLeapYear
  have ha : year % 4 = 0 := year_emod_4_zero year h1
  have h : q < 24 ∨ q = 24 := by omega

  cases h
  · rename_i hlt
    have hb : !year % 100 = 0  := by simp [year_emod_100_non_zero year h1 hle hlt]
    rw [ha, hb]
    simp
  · rename_i heq
    have hb : year % 400 = 0  := by simp [year_emod_400_zero year h1 heq (h3 heq)]
    rw [ha, hb]
    simp

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

  have hquad₁ : 0 ≤ quad := by omega
  have hquad₂ : quad ≤ 24 := by omega
  have hcent₃ (h1 : d' = 4*365) (h2 : quad = 24) : cent = 3 := by omega

  if h : d' < 4*365
  then
    let y := d' / 365
    let year := quadcent * 400 + cent * 100 + quad * 4 + y + 1
    toDayOfYear year d'
  else
    have hx : d' = 4*365 := by omega

    let year := quadcent * 400 + cent * 100 + quad * 4 + 4
    have hyear : year = quadcent * 400 + cent * 100 + quad * 4 + 4 := by omega
    ⟨year, .leap ⟨366, (by omega)⟩,
          (by simp [isLeapYear_of_sum year hyear hquad₁ hquad₂ (hcent₃ hx)])⟩

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
  | .Zero => Clip.clip 0 (if isLeapYear year then 365 else 364) dayOfYear
              (ite_ge _ _ _ _ 0 (Nat.zero_le _) (Nat.zero_le _))
  | .One => Clip.clip 1 (if isLeapYear year then 366 else 365) dayOfYear
              (ite_ge _ _ _ _ 1 (by simp_arith) (by simp_arith))

private def clipDayOfYearValid (b : YearBase) (year : Int) (dayOfYear : Int) : Option Nat :=
  match b with
  | .Zero => Clip.clip? 0 (if isLeapYear year then 365 else 364) dayOfYear
              (ite_ge _ _ _ _ 0 (Nat.zero_le _) (Nat.zero_le _))
  | .One => Clip.clip? 1 (if isLeapYear year then 366 else 365) dayOfYear
              (ite_ge _ _ _ _ 1 (by simp_arith) (by simp_arith))

private def toModifiedJulianDay (year : Int) (dayOfYear : Nat) : Int :=
  /- Gregorian serial date minus difference to modified julian date. -/
  let y := year - 1
  dayOfYear + (365 * y) + ( y / 4) - (y / 100) + ( y / 400)
    + ((default : Day).modifiedJulianDay -  1)

def firstDayOfYear (year : Int) : DayOfYear :=
    if isLeapYear year then .leap ⟨1, (by simp_arith)⟩ else .common ⟨1, (by simp_arith)⟩

def firstDayOfYearDate (year : Int) : OrdinalDate :=
  let firstDay : DayOfYear := if isLeapYear year
                       then .leap ⟨1, (by simp_arith)⟩
                       else .common ⟨1, (by simp_arith)⟩
  let isValid : match firstDay with
            | .common _ => isLeapYear year = false
            | .leap _ => isLeapYear year = true := by
    simp [firstDay]
    split
    · rename_i heq
      split at heq <;> try simp_all
    · rename_i heq
      split at heq <;> try simp_all

  ⟨year, firstDay, isValid⟩

/--  Convert from ISO 8601 Ordinal Date format.
Invalid day numbers will be clipped to the correct range (1 to 365 or 366). -/
def fromOrdinalDayOfYear (year : Int) (d : Time.Icc 1 366) : Day :=
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
  let d' ←  Clip.clip? 1 7 d (by simp_arith)

  -- first day of the year
  let firstDay := fromOrdinalDate (firstDayOfYearDate year)
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
  let d' ←  Clip.clip? 0 6 d (Nat.zero_le _)
  -- first day of the year
  let firstDay := fromOrdinalDate (firstDayOfYearDate year)
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
