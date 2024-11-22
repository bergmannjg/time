import Time
import Time.Data.List.Basic

/-!
## Verify date calculations

Main theorems:

* `Verify.OrdinalDate.toOrdinalDate_fromOrdinalDate_eq_id`
* `Verify.OrdinalDate.next_date_eq_add_one`
* `Verify.OrdinalDate.next_date_eq_mjd_add_one`

-/

namespace Verify.OrdinalDate

open Time
open Time.Notation

/-- Get next_date of `dt`:

*  if `dt.dayOfYear` is less then days in `dt.year` then add 1 to `dt.dayOfYear`,
*  else add 1 to `dt.Year` and set `dt.dayOfYear` to 1.
-/
def next_date (dt : OrdinalDate) : OrdinalDate :=
  match hm : dt.dayOfYear with
  | .common ⟨dy, hdy⟩ =>
    if h : dy < 365 then
      {dt with dayOfYear := .common ⟨dy + 1, by omega⟩,
               isValid := by have := dt.isValid; split <;> simp_all}
    else if hy : isLeapYear (dt.year + 1) then
      {dt with year := dt.year + 1,
               dayOfYear := .leap ⟨1, by simp⟩,
               isValid := by split <;> simp_all}
    else {dt with year := dt.year + 1, dayOfYear := .common ⟨1, by simp⟩,
                  isValid := by split <;> simp_all}
  | .leap ⟨dy, hdy⟩ =>
    if h : dy < 366 then
      {dt with dayOfYear := .leap ⟨dy + 1, by omega⟩,
               isValid := by have := dt.isValid; split <;> simp_all}
    else if hy : isLeapYear (dt.year + 1) then
      {dt with year := dt.year + 1,
               dayOfYear := .leap ⟨1, by simp⟩,
               isValid := by split <;> simp_all}
    else {dt with year := dt.year + 1, dayOfYear := .common ⟨1, by simp⟩,
                  isValid := by split <;> simp_all}

namespace DayOfYear

def lt_top (d : DayOfYear) : Bool :=
  match d with
  | .common ⟨dy, _⟩ => dy < 365
  | .leap ⟨dy, _⟩ =>  dy < 366

def incr (dt : OrdinalDate) (h : lt_top dt.dayOfYear) : OrdinalDate :=
  have hv := dt.isValid
  match hm : dt.dayOfYear with
  | .common ⟨dy, hdy⟩ =>
    ⟨dt.year, .common ⟨dy + 1, And.intro (by omega) (by
          simp [lt_top] at h
          split at h <;> simp_all
          simp [Icc, Subtype.ext_iff] at hm
          rw [hm] at h
          omega)⟩,
        by simp_all⟩
  | .leap ⟨dy, hdy⟩ =>
    ⟨dt.year, .leap ⟨dy + 1, And.intro (by omega) (by
          simp [lt_top] at h
          split at h <;> simp_all
          simp [Icc, Subtype.ext_iff] at hm
          rw [hm] at h
          omega)⟩,
        by simp_all⟩

end DayOfYear

theorem icc_eq (dt : OrdinalDate) (a : Icc 1 365) (h : dt.dayOfYear = DayOfYear.common a)
  : a = (dt.dayOfYear : Icc 1 366) := by
  simp [h]

theorem icc_eq' (dt : OrdinalDate) (a : Icc 1 366) (h : dt.dayOfYear = DayOfYear.leap a)
  : a = (dt.dayOfYear : Icc 1 366) := by
  simp [h]

theorem val_eq (dt : OrdinalDate) (a : Icc 1 365) (h : dt.dayOfYear = DayOfYear.common a)
  : a.val = (dt.dayOfYear : Icc 1 366).val := by
  have : a = (dt.dayOfYear : Icc 1 366) := by simp [h]
  exact Subtype.ext_iff.mp this

theorem val_eq' (dt : OrdinalDate) (a : Icc 1 366) (h : dt.dayOfYear = DayOfYear.leap a)
  : a.val = (dt.dayOfYear : Icc 1 366).val := by
  have : a = (dt.dayOfYear : Icc 1 366) := by simp [h]
  exact Subtype.ext_iff.mp this

theorem  mjd_incr_eq_next_date (dt : OrdinalDate)
    : (fromOrdinalDate (next_date dt)).modifiedJulianDay
      = (fromOrdinalDate dt).modifiedJulianDay + 1 := by
  unfold next_date fromOrdinalDate toModifiedJulianDay dayOfYear isLeapYear
  split <;> try simp_all
  · split <;> try simp_all
    · split <;> try simp_all
      · rename_i dy _ _  _ a _ heq
        have : dy + 1 = a.val := Subtype.ext_iff.mp heq
        rw [← this]
        omega
      · split <;> try simp_all
        rename_i a h heq _
        have hv := dt.isValid
        split at hv <;> try simp_all
        unfold isLeapYear at hv
        simp [] at hv
        have : 1 = a.val := Subtype.ext_iff.mp heq
        rw [← this]
        simp_arith
        omega
    · split <;> try simp_all
      split <;> try simp_all
      rename_i a _ heq _
      have : 1 = a.val := Subtype.ext_iff.mp heq
      rw [← this]
      simp_arith
      omega
  · split <;> try simp_all
    · split <;> try simp_all
      split <;> try simp_all
      rename_i dy _ _ _ a _ heq _
      have : 1 = a.val := Subtype.ext_iff.mp heq
      rw [← this]
      simp_arith
      have hv := dt.isValid
      split at hv <;> try simp_all
      unfold isLeapYear at hv
      simp [] at hv
      omega
    · split <;> try simp_all
      · rename_i dy _ _ _ a _ heq
        have : dy + 1 = a.val := Subtype.ext_iff.mp heq
        rw [← this]
        omega
      · split <;> try simp_all
        rename_i a _ heq _
        have : 1 = a.val := Subtype.ext_iff.mp heq
        rw [← this]
        simp_arith
        have hv := dt.isValid
        split at hv <;> try simp_all
        unfold isLeapYear at hv
        simp [] at hv
        omega

theorem transform_of_next_date_eq_add_one (dt : OrdinalDate)
    : toOrdinalDate (fromOrdinalDate (next_date dt))
      = OrdinalDate.addDays 1 dt := by
  have h : ⟨(fromOrdinalDate (next_date dt)).modifiedJulianDay⟩
            = fromOrdinalDate (next_date dt) := by simp
  rw [← h]
  have : (fromOrdinalDate (next_date dt)).modifiedJulianDay
      = (fromOrdinalDate dt).modifiedJulianDay + 1 := mjd_incr_eq_next_date dt
  rw [this]
  unfold OrdinalDate.addDays Day.addDays
  simp

theorem Int.self_mul_ediv_le {x k : Int} (h : k ≠ 0) : (x / k) * k ≤ x :=
  calc (x / k) * k
    _ ≤ (x / k) * k + x % k := Int.le_add_of_nonneg_right (Int.emod_nonneg x h)
    _ = x                   := Int.ediv_add_emod' _ _

theorem Icc.minus_one_add_le {b : Nat} (x : Time.Icc 1 b) : 0 ≤ (-1) + (x.val : Int) := by
  have := x.property.left
  omega

theorem Icc.minus_one_add_lt {a b : Nat} (x : Time.Icc a b) : (-1) + (x.val : Int) < b := by
  have := x.property.right
  omega

theorem assoc' (a b c : Int) : (a - c) + b = a + (-c + b) := by
  omega

def days_in_100_years_without_year_divisible_by_400 := 76*365+24*366

theorem days_in_100_years_without_year_divisible_by_400_eq
    : days_in_100_years_without_year_divisible_by_400 = 36524 := by rfl

def days_in_400_years := (4 * days_in_100_years_without_year_divisible_by_400 + 1)

theorem days_in_400_years_eq : days_in_400_years = 146097 := by rfl

def days_since_1_1_1 (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366) :=
  toModifiedJulianDay dt.year a.val - (default : Day).modifiedJulianDay

def days_since_1_1_1_mod_146097 (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366) :=
  365 * (dt.year - 1 - (dt.year - 1) / 400 * 400) + (dt.year - 1) / 4
  - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 - 1 + a.val

def days_since_1_1_1_mod_146097' (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366) :=
  days_since_1_1_1 dt a - ((dt.year-1) / 400) * 146097

theorem days_since_1_1_1_mod_146097'_eq  (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366)
    : days_since_1_1_1_mod_146097 dt a = days_since_1_1_1_mod_146097' dt a := by
  simp [days_since_1_1_1_mod_146097.eq_def, days_since_1_1_1_mod_146097'.eq_def, days_since_1_1_1]
  simp [toModifiedJulianDay, default]
  omega

def days_in_years_sub_one (year : Int) :=
  365 * year + year / 4 - year / 100

theorem days_in_400_years_sub_one_eq : days_in_years_sub_one 400 = days_in_400_years - 1 := by rfl

theorem days_in_400_years_sub_one_eq_mul (n : Int) : days_in_years_sub_one (n*400) = n*146096 := by
  simp [days_in_years_sub_one]
  omega

theorem days_in_400_years_sub_one_eq_mod (n : Int) : days_in_years_sub_one (n*400)%146096 = 0 := by
  simp [days_in_years_sub_one]
  omega

theorem days_since_1_1_1_mod_146097_le (dt : OrdinalDate)
    : 0 ≤ days_since_1_1_1_mod_146097 dt dt.dayOfYear := by
  simp [days_since_1_1_1_mod_146097, assoc']
  have : 0 ≤ 365 * (dt.year - 1 - (dt.year - 1) / 400 * 400) := by
    have : (dt.year - 1) / 400 * 400 ≤ dt.year - 1 := @Int.self_mul_ediv_le (dt.year - 1) 400 (by simp)
    omega
  have : 0 ≤ (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 := by
    have : ((dt.year - 1)*100) / 400 = (dt.year - 1) / 4 :=
      Int.mul_ediv_mul_of_pos_left (dt.year - 1) 4 (by simp)
    omega
  have : 0 ≤ (-(1:Int) + (dt.dayOfYear:Icc 1 366).val) := by
    exact @Icc.minus_one_add_le 366 dt.dayOfYear
  omega

theorem days_since_1_1_1_mod_146097_lt (dt : OrdinalDate)
    : days_since_1_1_1_mod_146097 dt dt.dayOfYear < 146097 :=  by
  let a : Icc (1:Nat) 366 := dt.dayOfYear
  have : 365 * ((dt.year-1) - ((dt.year-1) / 400) * 400)
          + ((dt.year-1) / 4 - ((dt.year-1) / 400) * 96 - (dt.year-1) / 100 - 1 + a.val)
        = days_since_1_1_1_mod_146097 dt a := by simp[days_since_1_1_1_mod_146097]; omega
  rw [← this]
  have : (dt.year-1) - ((dt.year-1) / 400) * 400 = (dt.year-1) % 400 := by omega
  rw [this]
  have : 146097
         = 365 * ((dt.year - 1) % 400) + (365 *(400 - (dt.year - 1) % 400) + 96 + 1) := by omega
  rw [this]

  have hlt : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 - 1 + a.val
          < 365 * (400 - (dt.year - 1) % 400) + 96 + 1 := by
    simp_all [instCoeDayOfYearIccOfNat]
    have h : a = dt.dayOfYear := by simp
    split at h
    · rename_i a _
      have h1 : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 - 1 + a.val
             < (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 + 365 := by
        rw [assoc']
        exact Int.add_lt_add_left (Icc.minus_one_add_lt a) ((dt.year - 1) / 4
                - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100)
      have h2 : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 + 365
             < 365 * (400 - (dt.year - 1) % 400) + 96 + 1 := by
        omega
      rw [h]
      exact Int.lt_of_le_of_lt (Int.le_of_lt h1) h2
    · rename_i a _
      have h1 : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 -1 + a.val
             < (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 + 366 := by
        rw [assoc']
        exact Int.add_lt_add_left (Icc.minus_one_add_lt a) ((dt.year - 1) / 4
                - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100)
      have h2 : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 + 366
             ≤ 365 * (400 - (dt.year - 1) % 400) + 96 + 1 := by
        omega
      rw [h]
      exact Int.lt_of_lt_of_le h1 h2
  have heq : 365 * ((dt.year - 1) % 400) ≤ 365 * ((dt.year - 1) % 400) := by omega
  exact Int.add_lt_add_of_le_of_lt heq hlt

theorem days_since_1_1_1_mul_mod (dt : OrdinalDate) (a : Time.Icc 1 366)
    : days_since_1_1_1 dt a
      = ((dt.year-1) / 400) * 146097 + days_since_1_1_1_mod_146097 dt a :=  by
  rw [days_since_1_1_1_mod_146097'_eq, days_since_1_1_1_mod_146097']
  omega

theorem days_since_1_1_1_mod_146097_div_eq_zero (dt : OrdinalDate)
    : days_since_1_1_1_mod_146097 dt dt.dayOfYear / 146097 = 0 := by
  exact Int.ediv_eq_zero_of_lt
          (days_since_1_1_1_mod_146097_le dt)
          (days_since_1_1_1_mod_146097_lt dt)

def quadcent (dt : OrdinalDate) := (dt.year-1) / 400

theorem days_since_1_1_1_div_eq (dt : OrdinalDate)
    : days_since_1_1_1 dt dt.dayOfYear / 146097 = quadcent dt :=  by
  simp [quadcent, days_since_1_1_1_mul_mod dt dt.dayOfYear]
  simp only [Int.add_comm ((dt.year - 1) / 400 * 146097)]
  simp [Int.add_mul_ediv_right]
  simp [days_since_1_1_1_mod_146097_div_eq_zero dt]

theorem days_since_1_1_1_mod_eq (dt : OrdinalDate)
    : days_since_1_1_1 dt dt.dayOfYear % 146097
    = days_since_1_1_1_mod_146097 dt dt.dayOfYear :=  by
  rw [days_since_1_1_1_mul_mod dt]
  simp only [Int.add_comm ((dt.year - 1) / 400 * 146097)]
  simp [Int.add_mul_emod_self]
  have := days_since_1_1_1_mod_146097_le dt
  exact Int.emod_eq_of_lt
          (days_since_1_1_1_mod_146097_le dt)
          (days_since_1_1_1_mod_146097_lt dt)

def cent (dt : OrdinalDate) := (dt.year - 1 - (quadcent dt) * 400) / 100

def days_since_1_1_1_mod_146097_mod_36524 (dt : OrdinalDate) (a : Time.Icc 1 366) :=
  365 * (dt.year - 1 - (quadcent dt) * 400 - (cent dt) * 100)
  - (cent dt) * 24 + (dt.year - 1) / 4
  - (quadcent dt) * 96 - (dt.year - 1) / 100 - 1 + a.val

theorem days_since_1_1_1_mod_146097_mul_mod (dt : OrdinalDate) (a : Time.Icc 1 366)
    : days_since_1_1_1_mod_146097 dt a
      = (cent dt) * 36524 + days_since_1_1_1_mod_146097_mod_36524 dt a := by
  simp [days_since_1_1_1_mod_146097, quadcent, cent, days_since_1_1_1_mod_146097_mod_36524]
  omega

theorem days_since_1_1_1_mod_146097_mod_36524_le (dt : OrdinalDate)
    : 0 ≤ days_since_1_1_1_mod_146097_mod_36524 dt dt.dayOfYear := by
  simp [days_since_1_1_1_mod_146097_mod_36524, quadcent, cent]
  split <;> try simp_all
  · rename_i a _
    have := a.property
    omega
  · rename_i a _
    have := a.property
    omega

theorem days_since_1_1_1_mod_146097_mod_36524_lt (dt : OrdinalDate)
  (h : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366))
    : days_since_1_1_1_mod_146097_mod_36524 dt dt.dayOfYear < 36524 := by
  simp [days_since_1_1_1_mod_146097_mod_36524, quadcent, cent]
  split <;> try simp_all
  · rename_i a _
    have := a.property
    omega
  · rename_i a _
    have := a.property
    have : dt.year % 400 = 0 ∨ ¬dt.year % 400 = 0 := by omega
    cases this
    · omega
    · have := dt.isValid
      simp [isLeapYear] at this
      split at this
      · have : a.val ≤ 365 := by simp_all
        omega
      · omega

theorem days_since_1_1_1_mod_146097_div_eq (dt : OrdinalDate)
  (h : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366))
    : days_since_1_1_1_mod_146097 dt dt.dayOfYear / 36524 = cent dt := by
  rw [days_since_1_1_1_mod_146097_mul_mod]
  rw [Int.add_comm]
  simp [Int.add_mul_ediv_right]
  have : days_since_1_1_1_mod_146097_mod_36524 dt dt.dayOfYear / 36524 = 0 := by
    have := days_since_1_1_1_mod_146097_mod_36524_le dt
    have := days_since_1_1_1_mod_146097_mod_36524_lt dt h
    omega
  simp_all

theorem cent_eq (dt : OrdinalDate) (h : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366))
    : cent dt = days_since_1_1_1_mod_146097 dt dt.dayOfYear / 36524 := by
  rw [← days_since_1_1_1_mod_eq dt]
  rw [days_since_1_1_1_mod_eq dt, days_since_1_1_1_mod_146097_div_eq dt h]

def dayOfYear_with_day_one (dt : OrdinalDate) : DayOfYear :=
  match dt.dayOfYear with
  | .leap _ => .leap ⟨1, by simp⟩
  | .common _ => .common ⟨1, by simp⟩

def dt_with_day_one (dt : OrdinalDate) : OrdinalDate :=
  have := dt.isValid
  match h : dt.dayOfYear with
  | .leap _ => ⟨dt.year, .leap ⟨1, by simp⟩, by simp_all⟩
  | .common _ => ⟨dt.year, .common ⟨1, by simp⟩, by simp_all⟩

def quad (dt : OrdinalDate) := (dt.year - 1 - (quadcent dt) * 400 - (cent dt) * 100) / 4

def c (dt : OrdinalDate) :=
  days_since_1_1_1_mod_146097 dt dt.dayOfYear - ((cent dt) * 36524)

def c_value_factor (dt : OrdinalDate) :=
  if ¬dt.year % 4 = 0 then (dt.year % 100) / 4
  else if ¬dt.year % 100 = 0 then (dt.year % 100) / 4 - 1
  else 24

theorem c_value_factor_eq (dt dt': OrdinalDate) (h : dt.year = dt'.year)
    : c_value_factor dt = c_value_factor dt' := by
  simp [c_value_factor]
  split <;> simp_all [h]

def c_value (dt : OrdinalDate) :=
  ((dt.year-1)%4)*365 + (c_value_factor dt)*1461 - 1 + (dt.dayOfYear:Icc 1 366).val

theorem year_of_dt_with_day_one_eq (dt : OrdinalDate)
  : dt.year = (dt_with_day_one dt).year := by
  simp [dt_with_day_one]
  split <;> simp_all

theorem dayOfYear_of_dt_with_day_one_eq (dt : OrdinalDate)
  : dayOfYear_with_day_one dt = (dt_with_day_one dt).dayOfYear := by
  simp [dt_with_day_one, dayOfYear_with_day_one]
  split <;> try simp_all
  · split <;> simp_all
  · split <;> simp_all

theorem dayOfYear_of_dt_with_day_one_val_eq (dt : OrdinalDate)
  : (dayOfYear_with_day_one dt:Icc 1 366).val = 1 := by
  simp [dayOfYear_with_day_one]
  split <;> try simp_all
  · rename_i heq
    split at heq <;> try simp_all
    rw [← heq]
  · rename_i heq
    split at heq <;> try simp_all
    rw [← heq]

theorem c_value_factor_of_dt_with_day_one_eq (dt : OrdinalDate)
  : c_value_factor dt = c_value_factor (dt_with_day_one dt) := by
  simp [c_value_factor]
  rw [year_of_dt_with_day_one_eq]

theorem c_value_of_dt_with_day_one_eq (dt : OrdinalDate)
  : c_value (dt_with_day_one dt) = ((dt.year-1)%4)*365 + (c_value_factor dt)*1461 := by
  simp [c_value]
  rw [← c_value_factor_of_dt_with_day_one_eq]
  simp [c_value_factor]
  split <;> try simp_all
  · rw [← dayOfYear_of_dt_with_day_one_eq]
    rw [dayOfYear_of_dt_with_day_one_val_eq]
    rw [← year_of_dt_with_day_one_eq]
    omega
  · rw [← dayOfYear_of_dt_with_day_one_eq]
    rw [dayOfYear_of_dt_with_day_one_val_eq]
    rw [← year_of_dt_with_day_one_eq]
    omega

theorem c_value_add_eq (dt : OrdinalDate)
    : c_value dt = c_value (dt_with_day_one dt) + (dt.dayOfYear:Icc 1 366).val - 1 := by
  rw [c_value_of_dt_with_day_one_eq]
  simp [c_value, c_value_factor, dt_with_day_one]
  split <;> try simp_all
  · split <;> try simp_all
    · omega
    · omega
  · split <;> try simp_all
    · omega
    · omega

theorem c_eq_c_value (dt : OrdinalDate) : c dt = c_value dt := by
  simp [c_value, c_value_factor, c, days_since_1_1_1_mod_146097, cent, quadcent]
  omega

def c_mod_1461 (dt : OrdinalDate) :=
  c dt - (quad dt) * 1461

def d' (dt : OrdinalDate) :=
  c dt % 1461

theorem d'_lt (dt : OrdinalDate) : d' dt < 1461:= by
  simp [d']
  omega

theorem c_value_div_eq (dt : OrdinalDate) : c_value dt / 1461 = c_value_factor dt := by
  rw [c_value_add_eq]
  rw [c_value_of_dt_with_day_one_eq]
  simp [c_value_factor]
  split <;> try simp_all
  · have : (dt.year - 1) % 4 * 365
            + (if dt.year % 100 = 0 then 24 else dt.year % 100 / 4 - 1) * 1461
            + (dt.dayOfYear:Icc 1 366).val - 1
        = (dt.year - 1) % 4 * 365 + (dt.dayOfYear:Icc 1 366).val - 1
          + (if dt.year % 100 = 0 then 24 else dt.year % 100 / 4 - 1) * 1461 := by
      omega
    rw [this]
    simp [Int.add_mul_ediv_right]
    have : (dt.dayOfYear:Icc 1 366).val ≤ 366 := (dt.dayOfYear:Icc 1 366).property.right
    omega
  · have : (dt.year - 1) % 4 * 365 + dt.year % 100 / 4 * 1461
            + (dt.dayOfYear:Icc 1 366).val - 1
        = (dt.year - 1) % 4 * 365 + (dt.dayOfYear:Icc 1 366).val - 1
           + dt.year % 100 / 4 * 1461:= by
      omega
    rw [this]
    simp [Int.add_mul_ediv_right]
    have := dt.isValid
    simp [isLeapYear] at this
    split at this
    · rename_i a _
      have : ((dt.year - 1) % 4 * 365 + a.val - 1) / 1461 = 0 := by
        have := a.property.left
        have := a.property.right
        omega
      rw [this]
      simp
    · have : dt.year % 4 = 0 := by simp [this]
      contradiction

theorem c_div_eq (dt : OrdinalDate) : c (dt_with_day_one dt) / 1461 = c dt / 1461 := by
  rw [c_eq_c_value dt]
  rw [c_eq_c_value (dt_with_day_one dt)]
  simp [c_value_of_dt_with_day_one_eq, c_value_factor]
  rw [c_value_div_eq dt]
  simp [c_value_factor]
  split <;> try simp_all
  · omega
  · omega

theorem c_one_div_eq_quad (dt : OrdinalDate) : (c (dt_with_day_one dt)) / 1461 = quad dt := by
  rw [c_eq_c_value (dt_with_day_one dt)]
  rw [c_value_div_eq]
  rw [c_value_factor_eq (dt_with_day_one dt) dt (Eq.symm (year_of_dt_with_day_one_eq dt))]
  simp [c_value_factor, quad, quadcent, cent]
  omega

theorem c_div_eq_quad (dt : OrdinalDate) : c dt / 1461 = quad dt := by
  rw [← c_div_eq dt]
  simp [c_one_div_eq_quad]

private theorem mod_146096_year_mod_400_eq (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366)
  (h : days_since_1_1_1_mod_146097 dt a = 146096) : dt.year % 400 = 0 := by
  simp [days_since_1_1_1_mod_146097] at h
  have : (-(1:Int) + a.val) ≤ 365 := by have := a.property.right; omega
  have : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 = 96 := by omega
  omega

theorem year_eq_if_mod_eq_146096 (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366)
  (h : days_since_1_1_1_mod_146097 dt a = 146096)
    : (quadcent dt) * 400 + 3*100 + 24*4 + 4 = dt.year := by
  simp [quadcent]
  have : dt.year % 400 = 0 := mod_146096_year_mod_400_eq dt a h
  omega

theorem mod_lt_146096_eq (dt : OrdinalDate)
  (h : days_since_1_1_1_mod_146097 dt (dt.dayOfYear:Icc 1 366) < 146096)
    : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366) := by
  simp [days_since_1_1_1_mod_146097] at h
  omega

theorem d'_add_eq (dt : OrdinalDate)
    : d' dt = ((dt.year-1)%4)*365 + (dt.dayOfYear:Icc 1 366).val - 1:= by
  simp [d', c_eq_c_value, c_value, c_value_factor]

  have : (dt.year - 1) % 4 * 365 +
          (if dt.year % 4 = 0 then if dt.year % 100 = 0 then 24 else dt.year % 100 / 4 - 1
           else dt.year % 100 / 4) * 1461
            - 1 + (dt.dayOfYear:Icc 1 366).val
       = (dt.year - 1) % 4 * 365 + (dt.dayOfYear:Icc 1 366).val - 1 +
          (if dt.year % 4 = 0 then if dt.year % 100 = 0 then 24 else dt.year % 100 / 4 - 1
           else dt.year % 100 / 4) * 1461
             := by
    omega
  rw [this]

  simp [Int.add_mul_emod_self]
  have := (dt.dayOfYear:Icc 1 366).property
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem days_eq_1460_mod_4_eq (dt : OrdinalDate) (hmod : d' dt = 1460)
    : dt.year % 4 = 0 := by
  have := d'_add_eq dt
  rw [hmod] at this
  have := (dt.dayOfYear:Icc 1 366).property
  have : (dt.dayOfYear:Icc 1 366).val ≤ 366 := by omega
  have : ¬(dt.dayOfYear:Icc 1 366).val < 366 := by omega
  omega

theorem day_eq_if_days_eq_1460 (dt : OrdinalDate) (hmod : d' dt = 1460)
    : (dt.dayOfYear:Icc 1 366).val = 366 := by
  have := d'_add_eq dt
  rw [hmod] at this
  have : dt.year % 4 = 0 ∨ ¬(dt.year % 4 = 0) := by omega
  cases this
  · omega
  · have := days_eq_1460_mod_4_eq dt hmod
    contradiction

theorem year_eq_if_days_eq_1460 (dt : OrdinalDate) (hmod : d' dt = 1460)
    : (quadcent dt)*400 + (cent dt)*100 + (quad dt)*4 + 4 = dt.year := by
  simp [quadcent, cent, quad, d']
  have : dt.year % 4 = 0 ∨ ¬(dt.year % 4 = 0) := by omega
  cases this
  · omega
  · have := days_eq_1460_mod_4_eq dt hmod
    contradiction

private theorem mod_146096_year_mod_4_eq (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366)
  (h : days_since_1_1_1_mod_146097 dt a = 146096) : dt.year % 4 = 0 := by
  simp [days_since_1_1_1_mod_146097] at h
  have : (-(1:Int) + a.val) ≤ 365 := by have := a.property.right; omega
  have : (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100 = 96 := by omega
  omega

private theorem isLeapYear_mod_146097_eq (dt : OrdinalDate)
  (hmod : (toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val
          - (default : Day).modifiedJulianDay) % 146097 = 146096)
    : isLeapYear dt.year = true := by
  rw [← days_since_1_1_1.eq_def dt dt.dayOfYear, days_since_1_1_1_mod_eq dt] at hmod
  simp [isLeapYear]
  have := mod_146096_year_mod_400_eq dt dt.dayOfYear hmod
  have := mod_146096_year_mod_4_eq dt dt.dayOfYear hmod
  simp_all

private theorem mod_146096_eq_day (dt : OrdinalDate) (a : Time.Icc (1:Nat) 366)
  (heq : dt.dayOfYear = DayOfYear.leap a) (h : days_since_1_1_1_mod_146097 dt a = 146096)
    : .leap ⟨366, by simp⟩ = dt.dayOfYear := by
  have : a = ⟨366, by simp⟩ := by
    simp [days_since_1_1_1_mod_146097] at h
    have : (-(1:Int) + a.val) ≤ 365 := by have := a.property.right; omega
    simp [Icc, Subtype.ext_iff]
    omega
  simp_all

theorem year_lt_mod_1460_eq (dt : OrdinalDate)
  (hNot : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366))
    : (toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay) / 146097 * 400
      + (toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay)
        % 146097 / 36524 * 100
      + ((toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay) % 146097
          - (toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay)
            % 146097 / 36524 * 36524) / 1461 * 4
      + ((toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay) % 146097
          - (toModifiedJulianDay dt.year (dt.dayOfYear:Icc 1 366).val - (default : Day).modifiedJulianDay)
            % 146097 / 36524 * 36524)
        % 1461 / 365 + 1
    = quadcent dt * 400 + cent dt * 100 + quad dt * 4 + d' dt / 365 + 1 := by

  rw [← days_since_1_1_1, days_since_1_1_1_div_eq]
  rw [days_since_1_1_1_mod_eq]
  rw [← cent_eq dt hNot, ← c.eq_def, c_div_eq_quad dt]
  rw [← d'.eq_def]

theorem d'_eq (dt : OrdinalDate) (h : ¬(dt.year % 400 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366))
    : (days_since_1_1_1 dt dt.dayOfYear % 146097 - days_since_1_1_1 dt dt.dayOfYear % 146097 / 36524 * 36524)
          % 1461 = d' dt := by
  rw [days_since_1_1_1_mod_eq dt]
  rw [← cent_eq dt h, ← c.eq_def, ← d'.eq_def]

theorem d'_lt_1460_eq (dt : OrdinalDate) (hlt : d' dt < 1460)
    : ¬(dt.year % 4 = 0 ∧ (dt.dayOfYear:Icc 1 366).val = 366) := by
  rw [d'_add_eq] at hlt
  by_contra
  rename_i h
  have : (dt.year - 1) % 4 = 3 := by omega
  rw [this] at hlt
  rw [h.right] at hlt
  omega

theorem d'_lt_1460_lt (dt : OrdinalDate) (hlt : d' dt < 1460)
    : (dt.dayOfYear:Icc 1 366).val < 366 := by
  have hv := dt.isValid
  simp [isLeapYear] at hv
  have hProperty := (dt.dayOfYear:Icc 1 366).property
  have hImp : dt.year % 4 = 0 → ¬((dt.dayOfYear:Icc 1 366).val = 366) :=
    not_and.mp (d'_lt_1460_eq dt hlt)
  have : dt.year % 4 = 0 ∨ ¬(dt.year % 4 = 0) := by omega
  cases this
  · rename_i h
    have := hImp h
    omega
  · rename_i h
    split at hv <;> try simp_all
    rename_i a _
    have := a.property
    omega

theorem d'_lt_1460_eq_year (dt : OrdinalDate) (hlt : d' dt < 1460)
    :  quadcent dt * 400 + cent dt * 100 + quad dt * 4 + d' dt / 365 + 1 = dt.year := by
  simp [quadcent, cent, quad]
  have : (dt.year - 1) % 4 = d' dt / 365 := by
    rw [d'_add_eq]
    have : (dt.year - 1) % 4 * 365 + (dt.dayOfYear:Icc 1 366).val - 1
         = (dt.dayOfYear:Icc 1 366).val - 1 + (dt.year - 1) % 4 * 365 := by
      omega
    rw [this]
    simp [Int.add_mul_ediv_right]
    have hProperty := (dt.dayOfYear:Icc 1 366).property
    have := d'_lt_1460_lt dt hlt
    omega
  rw [← this]
  omega

theorem d'_lt_1460_eq_day_common (dt : OrdinalDate) (h : dt.dayOfYear = DayOfYear.common a)
    : ((d' dt ) % 365 + 1).toNat = (dt.dayOfYear:Icc 1 366).val := by
  rw [d'_add_eq]
  split <;> try simp_all

  have : (dt.year - 1) % 4 * 365 + a.val - 1 = a.val - 1 + (dt.year - 1) % 4 * 365 := by
    omega
  rw [this]
  simp [Int.add_mul_ediv_right]
  have := a.property
  have : ((a.val:Int) - 1) % 365 = ↑a.val - 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp_all [this]

theorem d'_lt_1460_eq_day_leap (dt : OrdinalDate) (h : dt.dayOfYear = DayOfYear.leap a)
  (hlt : d' dt < 1460)
    : ((d' dt ) % 365 + 1).toNat = (dt.dayOfYear:Icc 1 366).val := by
  rw [d'_add_eq]
  split <;> try simp_all
  rename_i heq

  have : (dt.year - 1) % 4 * 365 + a.val - 1 = a.val - 1 + (dt.year - 1) % 4 * 365 := by
    omega
  rw [this]
  simp [Int.add_mul_ediv_right]

  have := d'_lt_1460_lt dt hlt
  simp [heq] at this
  have := a.property
  have : ((a.val:Int) - 1) % 365 = ↑a.val - 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp [this]

theorem toOrdinalDate_fromOrdinalDate_eq_id (dt : OrdinalDate)
    : toOrdinalDate (fromOrdinalDate dt) = dt := by
  unfold toOrdinalDate fromOrdinalDate dayOfYear toDayOfYear isLeapYear
  have hv := dt.isValid
  split at hv <;> try simp_all

  simp [OrdinalDate.ext_iff]
  split <;> try simp_all
  · rename_i a heq h
    rw [val_eq dt a heq] at h
    have hv' := isLeapYear_mod_146097_eq dt h
    simp_all [@ne_false_of_eq_true (isLeapYear dt.year)]
  · split <;> try simp_all
    · split <;> try simp_all
      · rename_i a heq hne hlt h
        have heq' : a.val = (dt.dayOfYear:Icc 1 366).val := by simp [heq]
        have hlt_146096 : days_since_1_1_1_mod_146097 dt (dt.dayOfYear:Icc 1 366) < 146096 := by
          rw [← days_since_1_1_1_mod_eq]
          rw [← days_since_1_1_1.eq_def dt (a:Icc 1 366)] at hne
          simp [heq]
          omega
        have hNot := mod_lt_146096_eq dt hlt_146096
        rw [heq'] at h
        rw [year_lt_mod_1460_eq dt hNot] at h
        rw [val_eq dt a heq] at hlt
        rw [d'_lt_1460_eq_year dt (by rwa [← days_since_1_1_1, d'_eq dt hNot] at hlt)] at h
        have hv' : isLeapYear dt.year := by
          simp [isLeapYear]
          exact h
        simp_all [@ne_false_of_eq_true (isLeapYear dt.year)]
      · rename_i a heq hne hlt _
        have heq' : a.val = (dt.dayOfYear:Icc 1 366).val := by simp [heq]
        have hlt_146096 : days_since_1_1_1_mod_146097 dt (dt.dayOfYear:Icc 1 366) < 146096 := by
          rw [← days_since_1_1_1_mod_eq]
          rw [← days_since_1_1_1.eq_def dt (a:Icc 1 366)] at hne
          simp [heq]
          omega
        have hNot := mod_lt_146096_eq dt hlt_146096
        exact And.intro
          (by
            rw [heq']
            rw [year_lt_mod_1460_eq dt hNot]
            rw [val_eq dt a heq] at hlt
            exact d'_lt_1460_eq_year dt (by rwa [← days_since_1_1_1, d'_eq dt hNot] at hlt))
          (by
            simp [Icc, Subtype.ext_iff]
            rw [heq']
            rw [← days_since_1_1_1, d'_eq dt hNot]
            rw [heq'] at hlt
            rw [← days_since_1_1_1, d'_eq dt hNot] at hlt
            exact d'_lt_1460_eq_day_common dt heq)
    · rename_i a heq hne h
      have hlt_146096 : days_since_1_1_1_mod_146097 dt (dt.dayOfYear:Icc 1 366) < 146096 := by
        rw [← days_since_1_1_1_mod_eq]
        rw [← days_since_1_1_1.eq_def dt (a:Icc 1 366)] at hne
        simp [heq]
        omega
      have hNot := mod_lt_146096_eq dt hlt_146096
      have hmod : d' dt = 1460 := by
        rw [val_eq dt a heq, ← days_since_1_1_1, d'_eq dt hNot] at h
        have := d'_lt dt
        omega
      have := day_eq_if_days_eq_1460 dt hmod
      have : (dt.dayOfYear:Icc 1 366).val ≤ 365 := by
        have hProperty := a.property
        have heq' : a.val = (dt.dayOfYear:Icc 1 366).val := by simp [heq]
        rw [heq'] at hProperty
        omega
      have : ¬((dt.dayOfYear:Icc 1 366).val = 366) := by omega
      contradiction
  · split <;> try simp_all
    · rename_i a heq h
      simp [OrdinalDate.ext_iff]
      rw [← days_since_1_1_1.eq_def dt a]
      rw [icc_eq' dt a heq]
      rw [days_since_1_1_1_div_eq dt]
      rw [← days_since_1_1_1.eq_def dt a] at h
      rw [icc_eq' dt a heq] at h
      simp [days_since_1_1_1_mod_eq dt] at h
      exact And.intro
              (year_eq_if_mod_eq_146096 dt dt.dayOfYear h)
              (by
                rw [← icc_eq' dt a heq] at h
                exact mod_146096_eq_day dt a heq h)
    · rename_i a heq hne
      have heq' : a = (dt.dayOfYear:Icc 1 366) := by simp [heq]
      have hlt_146096 : days_since_1_1_1_mod_146097 dt (dt.dayOfYear:Icc 1 366) < 146096 := by
        rw [← days_since_1_1_1_mod_eq]
        rw [← days_since_1_1_1] at hne
        rw [← heq']
        omega
      have hNot := mod_lt_146096_eq dt hlt_146096
      split <;> try simp_all
      · split <;> try simp_all
        · rename_i hlt hIsLeapYear
          simp [OrdinalDate.ext_iff]
          exact And.intro
            (by
              rw [heq']
              rw [year_lt_mod_1460_eq dt hNot]

              rw [val_eq' dt a heq] at hlt
              exact d'_lt_1460_eq_year dt (by rwa [← days_since_1_1_1, d'_eq dt hNot] at hlt)
            )
            (by
              rw [heq']
              rw [← days_since_1_1_1, d'_eq dt hNot]
              rw [heq]
              rw [heq']
              simp [DayOfYear, Icc, Subtype.ext_iff]
              rw [val_eq' dt a heq] at hlt
              exact d'_lt_1460_eq_day_leap dt heq
                (by rwa [← days_since_1_1_1, d'_eq dt hNot] at hlt)
            )
        · rename_i hlt hNotIsLeapYear
          simp [OrdinalDate.ext_iff]
          rw [heq'] at hNotIsLeapYear
          rw [year_lt_mod_1460_eq dt hNot] at hNotIsLeapYear
          rw [val_eq' dt a heq] at hlt
          rw [d'_lt_1460_eq_year dt (by rwa [← days_since_1_1_1, d'_eq dt hNot] at hlt)]
            at hNotIsLeapYear
          simp [isLeapYear] at hv
          contradiction
      · rename_i h
        simp [OrdinalDate.ext_iff]
        rw [val_eq' dt a heq]
        rw [← days_since_1_1_1.eq_def dt (dt.dayOfYear:Icc 1 366)]
        rw [days_since_1_1_1_div_eq]
        rw [days_since_1_1_1_mod_eq]
        rw [← cent_eq dt hNot, ← c.eq_def, c_div_eq_quad dt]
        have hmod : d' dt = 1460 := by
          rw [val_eq' dt a heq, ← days_since_1_1_1, d'_eq dt hNot] at h
          have := d'_lt dt
          omega
        simp [year_eq_if_days_eq_1460 dt hmod]
        have h' := day_eq_if_days_eq_1460 dt hmod
        simp [heq] at h'
        simp [heq]
        have : (⟨366, by simp⟩ : Icc 1 366).val = a.val := by simp [h']
        exact Subtype.ext_iff.mpr this

/-- `Verify.OrdinalDate.next_date` equals to `Time.OrdinalDate.addDays` 1. -/
theorem next_date_eq_add_one (dt : OrdinalDate) : next_date dt = OrdinalDate.addDays 1 dt := by
  have h := toOrdinalDate_fromOrdinalDate_eq_id (next_date dt)
  rw [← h]
  exact transform_of_next_date_eq_add_one dt

/-- `Verify.OrdinalDate.next_date` transforms to `Time.Day.addDays` 1. -/
theorem next_date_eq_mjd_add_one (dt : OrdinalDate)
    : next_date dt = (fromOrdinalDate dt |> Day.addDays 1 |> toOrdinalDate) := by
  have h := next_date_eq_add_one dt
  simp [ OrdinalDate.addDays] at h
  simp_all
