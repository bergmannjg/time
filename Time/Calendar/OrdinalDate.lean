import Mathlib.Tactic.NormNum
import Std.Data.Nat.Lemmas
import Std.Data.Int.Lemmas
import Std.Data.Int.DivMod
import Std.Data.Bool
import Time.Calendar.Days
import Time.Calendar.Private

namespace Time

inductive DayOfYear where
  | common : Set.Icc 1 365 -> DayOfYear
  | leap : Set.Icc 1 366 -> DayOfYear
  deriving Repr, BEq

instance : BEq DayOfYear where
  beq a b :=
    match a, b with
    | .common a, .common b => a.val = b.val
    | .leap a, .leap b => a.val = b.val
    | _, _ => false

instance : Coe DayOfYear (Set.Icc 1 366) where
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

private def toDayOfYear (year: Int) (d': Int) (_ : d' < 4*365) : OrdinalDate :=
  let yd' := d' % 365 + 1
  let yd := Int.toNat yd'

  have h1 : 0 < yd := by
    have ha : 0 <= d' % 365 := by simp [Int.emod_nonneg _]
    have hb : 0 < yd' := Int.lt_add_one_iff.mpr ha
    exact ((Int.toNat_lt_toNat hb).mpr hb)

  have h2 : yd <= 365 := by
    have ha : d' % 365 < 365 := by simp_arith [Int.emod_lt_of_pos _]
    have hb : yd' <= 365 := by simp [Int.add_one_le_iff.mpr ha]
    exact Int.toNat_le_toNat hb

  if h : isLeapYear year
  then ⟨year, .leap ⟨yd, And.intro h1 (Nat.le_step h2)⟩, (by simp_all)⟩
  else ⟨year, .common ⟨yd, And.intro h1 h2⟩, (by simp_all)⟩

theorem lt_of_ediv_eq {a b : Int} {n : Nat} (hb : 0 < b) (h : a / b = n) : a < b + n * b := by
  rw [← Int.emod_add_ediv a b, h]
  have hx : a % b < b := by exact Int.emod_lt_of_pos _ hb
  simp [Int.sub_lt_sub_right _ _]
  rw [Int.mul_comm]
  simp [hx]

theorem le_of_eq {n m : Int} (p : n = m) : n ≤ m :=
  p ▸ Int.le_refl n

lemma le_c {c b cent : Int} (hb₁ : 0 ≤ b) (hcent₀ : cent = min (b / 36524) 3 )
  (hcent₁ : 0 ≤ cent) (hcent₂ : cent < 4) (hc : c = b - (cent * 36524))
    : 0 ≤ c := by
  match hm : cent with
  | 0 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · simp [hb₁, hc, hm]
    · contradiction
  | 1 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · have hx : 1 * 36524 ≤ b := (Int.le_ediv_iff_mul_le (by simp_arith)).mp (by simp_all)
      simp [Int.mul_one] at hx
      calc
        0 ≤ b - 1 * 36524 := by simp [Int.sub_le_sub_right _ _]; simp [hx]
        _ = c := by rw [hc]
    · contradiction
  | 2 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · have hx : 2 * 36524 ≤ b := (Int.le_ediv_iff_mul_le (by simp_arith)).mp (by simp_all)
      calc
        0 ≤ b - 2 * 36524 := by simp [Int.sub_le_sub_right _ _]; simpa [hx]
        _ = c := by rw [hc]
    · contradiction
  | 3 =>
    have h1 : 3 ≤ b / 36524 := (Int.le_min.mp (le_of_eq hcent₀)).left
    have hx : 3 * 36524 ≤ b := (Int.le_ediv_iff_mul_le (by simp_arith)).mp (by simp_all)
    calc
      0 ≤ b - 3 * 36524 := by simp [Int.sub_le_sub_right _ _]; simpa [hx]
      _ = c := by rw [hc]

lemma c_lt {c b cent : Int} (hcent₀ : cent = min (b / 36524) 3 )
  (hcent₁ : 0 ≤ cent) (hcent₂ : cent < 3) (hc : c = b - (cent * 36524)) : c < 36524 := by
  match hm : cent with
  | 0 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · have hx : b < 36524 := lt_of_ediv_eq (by simp_arith) (Eq.symm hcent₀)
      calc
        c = b - (cent * 36524) := by simp [hc, hm]
        _ < 36524 := by simp [hx, hm]
    · contradiction
  | 1 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · have ha : b < 36524 + 36524 := lt_of_ediv_eq (by simp_arith) (Eq.symm hcent₀)
      have hb : c = b - 36524 := by simp [hm, hc]
      have hc : b - 36524 < 36524 := by apply (Int.sub_lt_sub_right ha 36524)
      rw [hb]
      simp [hc]
    · contradiction
  | 2 =>
    rw [Int.min_def] at hcent₀
    split at hcent₀
    · have ha : b < 36524 + 2 * 36524 :=
                lt_of_ediv_eq (by simp_arith) (Eq.symm hcent₀)
      have hb : c = b - 2*36524 := by simp [hm, hc]
      have hc : b - 2*36524 < 36524 := by apply (Int.sub_lt_sub_right ha (2*36524))
      rw [hb]
      simpa [hc]
    · contradiction

lemma c_le {c b cent : Int} (hb₂ : b < 146097) (hcent₀ : cent = min (b / 36524) 3 )
  (hcent₁ : 0 ≤ cent) (hcent₂ : cent < 4) (hc : c = b - (cent * 36524)) : c ≤ 36524 := by
  match hm : cent with
  | 0 | 1 | 2 => simp [Int.le_of_lt (c_lt hcent₀ hcent₁ (by simp_arith) hc)]
  | 3 => calc
      c = b - (cent * 36524) := by simp [hc, hm]
      _ = b - (3 * 36524) := by simp [hm]
      _ ≤ 146096 - (3 * 36524) := by
        have hb : b ≤ 146096 := Int.le_of_lt_add_one hb₂
        simp [hb]
      _ ≤ 36524  := by simp_arith

lemma cent_eq_of_c_eq {cent : Int} (c b : Int) (hcent₀ : cent = min (b / 36524) 3 )
  (hcent₁ : 0 ≤ cent) (hcent₂ : cent < 4) (hc : c = b - (cent * 36524)) (hceq : c = 36524)
    : cent = 3 := by
  match hm : cent with
  | 0 | 1 | 2 =>
    have : c < 36524 := c_lt hcent₀ hcent₁ (by simp_arith) hc
    have : c ≠ 36524 := Int.ne_of_lt this
    contradiction
  | 3 => simp

lemma year_emod_4_zero {qc cent q : Int} (year : Int) (h: year = qc * 400 + cent * 100 + q * 4 + 4)
    : year % 4 = 0 := by

  have ha : year = 4 * (qc * 100 + cent * 25 + q + 1) := calc
    year = qc * 400 + cent * 100 + q * 4 + 4 := by simp_all
       _ = qc * (100 * 4) + cent * (25 * 4) + q * 4 + 4 := by
                        have h1 : 25 * 4 = (100 : Int) := by simp_arith
                        have h2 : 100 * 4 = (400 : Int) := by simp_arith
                        rw [h1, h2]
       _ = qc * 100 * 4 + cent * 25 * 4 + q * 4 + 4 := by simp [Int.mul_assoc]
       _ = (qc * 100 + cent * 25 + q + 1) * 4 := by simp [Int.add_mul]
       _ = 4 * (qc * 100 + cent * 25 + q + 1) := by simp[Int.mul_comm]

  have hb : 4 ∣ year  := by simp [ha]
  simp [Int.emod_eq_zero_of_dvd hb]

lemma year_emod_400_zero {qc cent q : Int} (year : Int)
  (h1 : year = qc * 400 + cent * 100 + q * 4 + 4) (h2 : q = 24) (h3 : cent = 3)
    : year % 400 = 0 := by
  rw [Int.add_assoc, Int.add_assoc] at h1
  rw [h2] at h1
  rw [h3] at h1
  have : (24 : Int) * 4 + 4 = 100 := by simp_arith
  rw [this] at h1
  have : (3 : Int) * 100 + 100 = 400 := by simp_arith
  rw [this] at h1
  simp only [h1, Int.add_emod_self, Int.mul_emod_left]

lemma year_emod_100_non_zero {qc cent q : Int} (year : Int)
  (h1: year = qc * 400 + cent * 100 + q * 4 + 4) (hle : 0 ≤ q)  (h2 : q < 24) : year % 100 ≠ 0 := by
  rw [Int.add_assoc] at h1
  have h2 : q * 4 + 4 < 100 := by
    have ha : q * 4 + 4 < 24 * 4 + 4 := by
      apply (Int.add_lt_add_right)
      apply (Int.mul_lt_mul_of_pos_right h2 _)
      simp
    simpa [ha]
  have h3 : (qc * 400 + cent * 100) % 100 = 0 := by
    have : (400 : Int) = 4 * 100 := by simp_arith
    rw [this]
    rw [← Int.mul_assoc]
    simp [Int.mul]
  have ha : 4 ≤ q * 4 + 4 := by
    have : 0 ≤ q * 4 := by
      simp [@Int.mul_nonneg q 4 hle (by simp_arith)]
    simp [Int.le_add_of_nonneg_left this]
  have hb : 0 < q * 4 + 4 := Int.lt_of_lt_of_le (by simp) ha
  have h4 : (0 + (q * 4 + 4)) % 100 = q * 4 + 4 := by
    simp [Int.emod_eq_of_lt (Int.le_of_lt hb) h2]

  rw [h1]
  rw [← Int.emod_add_emod]
  rw [h3, h4]
  apply Int.ne_of_gt hb

theorem isLeapYear_of_sum {qc cent q : Int} (year : Int)
  (h1: year = qc * 400 + cent * 100 + q * 4 + 4) (hle : 0 ≤ q) (h2 : q ≤ 24)
  (h3 : q = 24 -> cent = 3) : isLeapYear year := by
  unfold isLeapYear
  have ha : year % 4 = 0 := year_emod_4_zero year h1
  have h : q < 24 ∨ q = 24 := by
    rcases Int.lt_trichotomy q 24 with lt | rfl | gt
    · exact Or.inl lt
    · simp_all
    · have : 24 < 24 := Int.lt_of_lt_of_le gt h2
      contradiction

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

  have hb₁ : 0 ≤ b := by simp_arith [Int.emod_nonneg _]
  have hb₂ : b < 146097 := by simp_arith [Int.emod_lt_of_pos _]
  have hb₃ : 0 ≤ b / 36524 := Int.le_ediv_of_mul_le (by simp_arith) (by simp_arith [hb₁])
  have hb₄ : b ≤ 146096 := Int.le_of_lt_add_one
        (by (have : (146096 + 1 : Int) = 146097 := by simp_arith); rw [this]; simp [hb₂])
  have hcent₁ : 0 ≤ cent := Int.le_min.mpr (And.intro hb₃ (by simp_arith))
  have hcent₂ : cent < 4 := by simp [cent]
  have hc₁ : 0 ≤ c := le_c hb₁ (by simp) hcent₁ hcent₂ (by simp)
  have hc₂ : c ≤ 36524 := c_le hb₂ (by simp) hcent₁ hcent₂ (by simp)
  have hquad₁ : 0 ≤ quad := Int.le_ediv_of_mul_le (by simp_arith)
        (by rw [Int.mul_comm, Int.mul_zero]; simp_all [hc₁])
  have hquad₂ : quad ≤ 24 := calc
        quad = c / 1461 := by simp
           _ ≤ 36524 / 1461 := Int.ediv_le_ediv (by simp_arith) hc₂
           _ = 24 := by simp_arith
  have hcent₃ (h1 : d' = 4*365)  (h2 : quad = 24) : cent = 3 := by
    have : c = 36524  := by
      have hquad : quad = c / 1461 := by simp
      have hd' : d' = c % 1461 := by simp
      have hx : c % 1461 + 1461 * quad = c := by simp [Int.emod_add_ediv c 1461, hquad]
      rw [← hd', h1, h2] at hx
      have hy : 4 * 365 + 1461 * 24 = (36524:Int) := by simp_arith
      rw [hy] at hx
      exact (Eq.symm hx)
    apply (cent_eq_of_c_eq c b (by simp) hcent₁ hcent₂ (by simp) this)

  have hd' : d' < 1461 := by simp_arith [Int.emod_lt_of_pos _]

  have h1 : 0 <= d' := by simp [Int.emod_nonneg _]
  have h2 : d' < 3*365 + 366 := by
    have ha : d' < 1461 := by simp_arith [Int.emod_lt_of_pos _]
    exact ha

  if h : d' < 4*365
  then
    let y := d' / 365
    let year := quadcent * 400 + cent * 100 + quad * 4 + y + 1
    toDayOfYear year d' h
  else
    have hx : d' = 4*365 := by
      have ha : 4*365 ≤ d' := not_lt.mp h
      have hb : d' ≤ 4*365 := by
        have ha : (3*365:Int) + 366 = 4*365 + 1 := by simp_arith
        have hc : d' < 4*365 + 1 := ha ▸ h2
        simp [Int.le_of_lt_add_one hc]
        apply Int.le_of_lt_add_one
        simp [hd']
      simp [Int.le_antisymm ha hb]

    let yd : Nat := d'.toNat - 3*365 + 1

    have hy : yd = 366 := by
      let hyd : yd = d'.toNat - 3*365 + 1 := by simp
      rw [hyd, hx]
      simp_arith

    have h1 : 0 < yd := by simp_arith
    have h2 : yd ≤ 366 := Nat.le_of_eq hy

    let year := quadcent * 400 + cent * 100 + quad * 4 + 4
    have hyear : year = quadcent * 400 + cent * 100 + quad * 4 + 4 := by simp
    ⟨year, .leap ⟨yd, And.intro h1 h2⟩,
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
  let d' ←  Private.clipValid 0 6 d (by norm_num1)
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
