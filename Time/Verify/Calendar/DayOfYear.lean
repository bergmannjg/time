import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.MonthLength

/-!
## Theorems about `Time.dy` properties

Main theorems:

* `Verify.DayOfYear.dy_eq_dy'`
* `Verify.DayOfYear.Notation.«termDy'MonthEq%_»`
* `Verify.DayOfYear.Notation.«termDy'MonthDayEq%_»`

-/

namespace Verify
namespace DayOfYear

open Time
open MonthLength

/-- Get day of year of last day of all months by `Time.dy`-/
def dyOfLastDayOfMonth_map (isleap : Bool) : List Nat :=
  List.range' 1 12 |> List.map (fun m => Time.dyOfLastDayOfMonth isleap m)

/-- Compute `Time.dy` for all days in a year -/
def dy_map (isleap : Bool) : List Nat :=
  monthLengths isleap
  |> List.map (fun (m, ml) => List.range' 1 ml |> List.map (fun d => Time.dy isleap m d))
  |> List.flatten

def dy'_map (isleap : Bool) : List Nat :=
  monthLengths isleap
  |> List.attach
  |> List.map (fun a =>
      List.range' 1 a.val.2 |> List.attach
      |> List.map (fun (d :  { x // x ∈ List.range' 1 a.val.snd }) =>
            let month : Icc 1 12 := ⟨a.val.1, by
                have := Time.monthLengths_month_in isleap a a.property; omega⟩
            let day : Icc 1 31 := ⟨d.val, by
                have := monthLengths_days_in isleap a a.property
                have := List.mem_range'_1.mp d.property
                omega⟩
            Time.dy' isleap month day))
  |> List.flatten

/-
set_option maxRecDepth 1200 in
theorem dy'_map_eq_dy_map (isleap : Bool) : dy'_map isleap = dy_map isleap := by
  cases isleap <;> simp_arith

set_option maxRecDepth 1200 in
theorem dy_map_eq (isleap : Bool)
    : dy_map isleap = List.range' 1 (if isleap then 366 else 365) := by
  cases isleap <;> simp_arith

set_option maxRecDepth 1500 in
theorem dy_map_size_eq (isleap : Bool)
    : List.length (dy_map isleap) = if isleap then 366 else 365 := by
  cases isleap <;> simp_arith
-/

/-- Get first day of month as day of year by lookup in `monthLastDayAsDayOfYear`
    is equal to compute by `Time.dy` -/
theorem monthFirstDayAsDayOfYear_eq_dy (isleap : Bool)
    : ∀ a ∈ monthLastDayAsDayOfYear' isleap, a.2.1 = Time.dy isleap a.1 1 := by
  cases isleap <;> simp_arith

/-- Get last day of month as day of year by lookup in `monthLastDayAsDayOfYear`
    is equal to compute by `Time.dy` -/
theorem monthLastDayAsDayOfYear_eq_dy (isleap : Bool)
    : ∀ a ∈ monthLastDayAsDayOfYear' isleap, a.2.2 = Time.dyOfLastDayOfMonth isleap a.1 := by
  cases isleap <;> simp_arith

theorem dy_eq_incr (isleap : Bool) (m : Icc 1 12) (d : Icc 1 31)
    : Time.dy isleap m.val d.val = (Time.dy isleap m.val 1) + d.val - 1 := by
  unfold Time.dy
  simp_arith
  have := d.property.left
  have := m.property.left
  omega

theorem dy_eq_dy' (isleap : Bool) (m : Icc 1 12) (d : Icc 1 31)
    : Time.dy isleap m.val d.val = Time.dy' isleap m d := by
  unfold Time.dy'
  generalize memOfMonth isleap m = a
  simp [monthFirstDayAsDayOfYear_eq_dy isleap a a.property.left, dy_eq_incr, a.property.right]

theorem lt_dy'_lt (isleap : Bool) (month : Icc 1 12) (day1 day2 : Icc 1 31)
  (hlt : day1.val < day2.val)
    : (dy' isleap month day1) < (dy' isleap month day2) := by
  simp [Time.dy']
  have := day1.property
  omega

theorem dy'_hlt {dt : Date}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd)
    : Time.dy' (isLeapYear dt.Year) dt.Month dt.Day
    < Time.dy' (isLeapYear dt.Year) dt.Month ⟨ml.val.snd,
        by exact monthLengths_days_in (isLeapYear dt.Year) ml.val ml.property.left⟩ := by
  exact lt_dy'_lt (isLeapYear dt.Year) dt.Month dt.Day ⟨ml.val.snd,
        by exact monthLengths_days_in (isLeapYear dt.Year) ml.val ml.property.left⟩ h

theorem dy'_hle {dt : Date}
  (ml : { m // monthLengthsOfDate m dt })
    : Time.dy' (isLeapYear dt.Year) dt.Month ⟨ml.val.snd,
        by exact monthLengths_days_in (isLeapYear dt.Year) ml.val ml.property.left⟩
    ≤ if isLeapYear dt.Year then 366 else 365  := by
  exact Time.dy'_le (isLeapYear dt.Year) dt.Month ⟨ml.val.snd,
        by exact monthLengths_days_in (isLeapYear dt.Year) ml.val ml.property.left⟩

theorem dy'_hlt' {dt : Date}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd)
    : Time.dy' (isLeapYear dt.Year) dt.Month dt.Day
    < if isLeapYear dt.Year then 366 else 365 := by
  exact Nat.lt_of_lt_of_le (dy'_hlt h) (dy'_hle ml)

theorem dy'_add_one_hle {dt : Date}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd)
    : Time.dy' (isLeapYear dt.Year) dt.Month dt.Day + 1
    ≤ if isLeapYear dt.Year then 366 else 365 := by
  exact Nat.lt_of_lt_of_le (dy'_hlt h) (dy'_hle ml)

theorem dy'_lt_of_month_lt {dt : Date}
  (h : dt.Month.val < 12)
    : Time.dy' (isLeapYear dt.Year) dt.Month dt.Day
    < if isLeapYear dt.Year then 366 else 365 := by
  simp [dy']
  split <;> try simp_all
  · rename_i h
    rw [h]
    generalize memOfMonth true dt.Month = a
    have : a.val.fst < 12 := by omega
    have hlt := monthLastDayAsDayOfYear'_month_lt_12_lt true dt a this
    simp [] at hlt
    have := dt.Day.property
    omega
  · rename_i h
    rw [h]
    generalize memOfMonth false dt.Month = a
    have : a.val.fst < 12 := by omega
    have hlt := monthLastDayAsDayOfYear'_month_lt_12_lt false dt a this
    simp [] at hlt
    have := dt.Day.property
    omega

theorem dy_lt_of_month_lt {dt : Date} (h : dt.Month.val < 12)
    : match (dateToOrdinalDate dt).dayOfYear with
      | .common dy => dy.val < 365
      | .leap dy => dy.val < 366 := by
  simp [dateToOrdinalDate]
  split <;> try simp_all
  · rename_i dy heq'
    split at heq' <;> simp_all
    rename_i hl
    simp [Icc, Subtype.ext_iff] at heq'
    have := @dy'_lt_of_month_lt dt h
    rw [← dy_eq_dy'] at this
    simp [hl] at this
    omega
  · rename_i dy heq'
    split at heq' <;> simp_all
    simp [Icc, Subtype.ext_iff] at heq'
    rename_i hl
    have := @dy'_lt_of_month_lt dt h
    rw [← dy_eq_dy'] at this
    simp [hl] at this
    omega

theorem dy_lt_of_day_lt {dt : Date}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd)
    : match (dateToOrdinalDate dt).dayOfYear with
      | .common dy => dy.val < 365
      | .leap dy => dy.val < 366 := by
  simp [dateToOrdinalDate]
  split <;> try simp_all
  · rename_i dy heq'
    split at heq' <;> simp_all
    rename_i hNotLeapYear
    have hl : isLeapYear dt.Year = false := by simp [hNotLeapYear]
    have hmem := ml.property.left
    simp [hl] at hmem
    simp [Icc, Subtype.ext_iff] at heq'
    have hlt := dy'_hlt h
    simp [hl] at hlt
    have hle := dy'_hle ml
    simp [hl] at hle
    rw [dy_eq_dy'] at heq'
    rw [heq'] at hlt
    exact Nat.lt_of_lt_of_le hlt hle
  · rename_i dy heq'
    split at heq' <;> simp_all
    rename_i hLeapYear
    have hl : isLeapYear dt.Year = true := by simp [hLeapYear]
    have hmem := ml.property.left
    simp [hl] at hmem
    simp [Icc, Subtype.ext_iff] at heq'
    have hlt := dy'_hlt h
    simp [hl] at hlt
    have hle := dy'_hle ml
    simp [hl] at hle
    rw [dy_eq_dy'] at heq'
    rw [heq'] at hlt
    exact Nat.lt_of_lt_of_le hlt hle

theorem dy_lt_of_day_or_month_lt {dt : Date}
  {ml : { m // monthLengthsOfDate m dt }}
  (h : dt.Day.val < ml.val.snd ∨ dt.Month.val < 12)
    : match (dateToOrdinalDate dt).dayOfYear with
      | .common dy => dy.val < 365
      | .leap dy => dy.val < 366 := by
  cases h
  · rename_i h
    exact @dy_lt_of_day_lt dt ml h
  · rename_i h
    exact @dy_lt_of_month_lt dt h

theorem dy'_month_1_eq (dt : Date) (isleap : Bool)
  (h : dy' isleap dt.Month dt.Day ≤ 30)
    : 1 = dt.Month.val := by
  simp [dy'] at h
  generalize memOfMonth isleap dt.Month = a at h
  have := monthLastDayAsDayOfYear'_month_1_eq dt isleap a (by have := dt.Day.property.left; omega)
  rwa [a.property.right] at this

theorem dy'_month_1_day_eq (dt : Date) (isleap : Bool)
  (h : dy' isleap dt.Month dt.Day ≤ 30)
    : dy' isleap dt.Month dt.Day = dt.Day.val := by
  have : 1 = dt.Month.val := dy'_month_1_eq dt isleap h
  simp [dy']
  generalize memOfMonth isleap dt.Month = a
  have := monthLastDayAsDayOfYear'_day_of_month_1_eq dt isleap a (by omega)
  omega

theorem dy'_day_n_eq (isleap : Bool)
  (i : Fin (monthLastDayAsDayOfYear' isleap).length) (hle : 1 ≤ i.val)
  (a : Nat × Nat × Nat)
  (h : (monthLastDayAsDayOfYear' isleap)[i.val] = a)
    : (monthLastDayAsDayOfYear' isleap)[i.val - 1].snd.snd + 1 = a.snd.fst := by
  rw [← h]
  exact (monthLastDayAsDayOfYear'_pred_snd_incr_eq_fst isleap i (by omega)).symm

theorem dy'_day_n_eq_incr (isleap : Bool) (dt : Date)
  (i i' : Fin (monthLastDayAsDayOfYear' isleap).length)
  (hi : i.val - 1 = i'.val)
  (a : Nat × Nat × Nat)
  (h1 : (monthLastDayAsDayOfYear' isleap)[i'.val] = a)
  (h2 : dt.Day.val = (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd
                      - (monthLastDayAsDayOfYear' isleap)[i'.val].snd.fst + 1)
  : a.snd.fst + dt.Day.val
    - ((monthLastDayAsDayOfYear isleap).get ⟨i.val - 1, by
          rw [hi]
          have := i'.isLt
          simp_all⟩).snd = 1 := by
  rw [← h1, h2]
  have hi : (⟨i.val - 1,
            by rw [hi]; have := i'.isLt; simp_all⟩ : Fin (monthLastDayAsDayOfYear isleap).length)
          = i' := by
    simp [Fin.ext_iff]
    omega
  rw [hi]
  have : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.fst
          < (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd :=
    monthLastDayAsDayOfYear'_fst_lt_snd isleap i'

  suffices h : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd + 1
      - ((monthLastDayAsDayOfYear isleap).get i').snd = 1 by omega

  suffices h : (monthLastDayAsDayOfYear' isleap)[i'.val].snd.snd
        = ((monthLastDayAsDayOfYear isleap).get i').snd by omega

  exact monthLastDayAsDayOfYear'_snd_eq isleap i'

theorem dy'_month_n_and_day_eq (dt : Date) (isleap : Bool)
  (i : Fin (monthLastDayAsDayOfYear isleap).length) (hle : 1 ≤ i.val)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (h1 : ((monthLastDayAsDayOfYear isleap).get ⟨i-1, by omega⟩).snd < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day + 1 ≤ ((monthLastDayAsDayOfYear isleap).get i).snd)
    : i + 1 = dt.Month.val
    ∧ dt.Day.val + 1
      = dy' isleap dt.Month dt.Day + 1
        - ((monthLastDayAsDayOfYear isleap).get ⟨i-1, by omega⟩).snd:= by
  simp only [dy'] at h1
  simp only [dy'] at h2
  simp only [dy']
  generalize memOfMonth isleap dt.Month = a at *
  have heq1 := monthLastDayAsDayOfYear_snd_eq isleap ⟨i-1, by omega⟩
  have heq2  := monthLastDayAsDayOfYear_snd_eq isleap i
  rw [heq1] at h1
  rw [heq2] at h2

  simp at h1
  simp at h2

  have hlt' : i < (monthLastDayAsDayOfYear' isleap).length := by
    have := monthLastDayAsDayOfYear_length_eq_12 isleap
    have := monthLastDayAsDayOfYear'_length_eq_12 isleap
    omega

  have h1 : (monthLastDayAsDayOfYear' isleap)[i.val - 1].snd.snd + 1
            ≤  a.val.snd.fst + dt.Day.val - 1 + 1 := by omega
  have := monthLastDayAsDayOfYear'_pred_snd_incr_eq_fst isleap i hle
  simp at this
  rw [← this] at h1

  have ⟨i', h'⟩ := List.get_of_mem a.property.left
  have h'month : ((monthLastDayAsDayOfYear' isleap).get i').fst = dt.Month.val := by
    rw [← a.property.right]
    simp_all

  rw [← h'] at h1
  rw [← h'] at h2
  have : ⟨i, hlt'⟩ = i' := monthLastDayAsDayOfYear'_index_eq i i' dt hl hml h h'month
    (by
      have := dt.Day.property.left
      have : ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val - 1 + 1
           = ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val := by omega
      rw [this] at h1
      simp_all)
    (by
      have := dt.Day.property.left
      have : ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val - 1 + 1
           = ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val := by omega
      simp_all)

  have h1 : (monthLastDayAsDayOfYear' isleap).get ⟨i, hlt'⟩ = a.val := by simp_all
  have h2 := monthLastDayAsDayOfYear'_month_eq isleap ⟨i, hlt'⟩

  simp_all

  suffices h : (monthLastDayAsDayOfYear' isleap)[↑i - 1].snd.snd + 1 = a.val.snd.fst by
    omega

  rw [← this] at h'
  exact dy'_day_n_eq isleap i (by simp_all) a.val h'

theorem dy'_month_n_and_day_eq_incr (dt : Date) (isleap : Bool)
  (i : Fin (monthLastDayAsDayOfYear isleap).length) (hle : 1 ≤ i.val)
  (hl : isLeapYear dt.Year = isleap)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val = ml.val.snd)
  (h1 : ((monthLastDayAsDayOfYear isleap).get ⟨i-1, by omega⟩).snd < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day + 1 ≤ ((monthLastDayAsDayOfYear isleap).get i).snd)
    : i = dt.Month.val
    ∧ dy' isleap dt.Month dt.Day + 1
        - ((monthLastDayAsDayOfYear isleap).get ⟨i-1, by omega⟩).snd = 1 := by
  simp only [dy'] at h1
  simp only [dy'] at h2
  simp only [dy']
  generalize memOfMonth isleap dt.Month = a at *
  have heq1 := monthLastDayAsDayOfYear_snd_eq isleap ⟨i-1, by omega⟩
  have heq2  := monthLastDayAsDayOfYear_snd_eq isleap i
  rw [heq1] at h1
  rw [heq2] at h2

  simp at h1
  simp at h2

  have hlt' : i < (monthLastDayAsDayOfYear' isleap).length := by
    have := monthLastDayAsDayOfYear_length_eq_12 isleap
    have := monthLastDayAsDayOfYear'_length_eq_12 isleap
    omega

  have h1 : (monthLastDayAsDayOfYear' isleap)[i.val - 1].snd.snd + 1
            ≤  a.val.snd.fst + dt.Day.val - 1 + 1 := by omega
  have := monthLastDayAsDayOfYear'_pred_snd_incr_eq_fst isleap i hle
  simp at this
  rw [← this] at h1

  have ⟨i', h'⟩ := List.get_of_mem a.property.left
  have h'month : ((monthLastDayAsDayOfYear' isleap).get i').fst = dt.Month.val := by
    rw [← a.property.right]
    simp_all

  rw [← h'] at h1
  rw [← h'] at h2
  have hi : i.val - 1 = i'.val := monthLastDayAsDayOfYear'_index_eq_of_last_day_in_month i i'
                                dt hl hml h h'month
    (by
      have := dt.Day.property.left
      have : ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val - 1 + 1
           = ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val := by omega
      rw [this] at h1
      simp_all)
    (by
      have := dt.Day.property.left
      have : ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val - 1 + 1
           = ((monthLastDayAsDayOfYear' isleap).get i').snd.fst + dt.Day.val := by omega
      simp_all)

  have h1 : (monthLastDayAsDayOfYear' isleap).get i' = a.val := by simp_all
  have h2 := monthLastDayAsDayOfYear'_month_eq isleap i'

  exact And.intro
    (by
      have : i.val = i'.val + 1 := by omega
      simp_all)
    (by
      suffices h : a.val.snd.fst + dt.Day.val
                     - ((monthLastDayAsDayOfYear isleap).get ⟨i.val - 1, by omega⟩).snd
                   = 1 by
        omega

      have := monthLastDayAsDayOfYear'_sub_eq_incr i' dt hl hml h h'month
      exact dy'_day_n_eq_incr isleap dt i i' hi a.val (by simp_all) this)
