import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.MonthLength

/-!
## Theorems about `Time.dy'` properties
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
  |> List.join

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
  |> List.join

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

/-- Get last day of month as day of year by lookup in `monthLastDayAsDayOfYear`
    is equal to compute by `Time.dy` -/
theorem monthLastDayAsDayOfYear_eq_dy (isleap : Bool)
    : (monthLastDayAsDayOfYear isleap |> List.map (fun x => x.2))
    = dyOfLastDayOfMonth_map isleap := by
  cases isleap <;> simp_arith

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
    let a := memOfMonth true dt.Month
    have : a = memOfMonth true dt.Month := by simp
    rw [← this]
    have : a.val.fst < 12 := by omega
    have hlt := monthLastDayAsDayOfYear'_month_lt_12_lt true dt a this
    simp [] at hlt
    have := dt.Day.property
    omega
  · rename_i h
    rw [h]
    let a := memOfMonth false dt.Month
    have : a = memOfMonth false dt.Month := by simp
    rw [← this]
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
    simp [hl] at this
    omega
  · rename_i dy heq'
    split at heq' <;> simp_all
    simp [Icc, Subtype.ext_iff] at heq'
    rename_i hl
    have := @dy'_lt_of_month_lt dt h
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
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h
  have := monthLastDayAsDayOfYear'_month_1_eq dt isleap a (by have := dt.Day.property.left; omega)
  rwa [a.property.right] at this

theorem dy'_month_1_day_eq (dt : Date) (isleap : Bool)
  (h : dy' isleap dt.Month dt.Day ≤ 30)
    : dy' isleap dt.Month dt.Day = dt.Day.val := by
  have : 1 = dt.Month.val := dy'_month_1_eq dt isleap h
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := monthLastDayAsDayOfYear'_day_of_month_1_eq dt isleap a (by omega)
  omega

theorem dy'_month_2_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : 31 < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 59 else 58)
    : 2 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_2_eq dt false a  (by omega) (by omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_2_eq dt true a  (by omega) (by omega)]

theorem dy'_month_2_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : 31 < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 59 else 58)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - 30 := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_2_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_2_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

theorem month_2_if_lt {dt : Date} (isLeap : Bool)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hl : isLeapYear dt.Year = isLeap)
    : dt.Month.val = 2 → dt.Day.val < if isLeap then 29 else 28 := by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := @month_2_if_eq ml.val isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all

theorem dy'_month_3_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 2 → dt.Day.val < (if isleap then 29 else 28))
  (h1 : (if isleap then 60 else 59) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 90 else 89)
    : 3 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1 <;> simp [] at h2 <;> simp [] at h'
  · have h' : a.val.fst = 2 → 32 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_3_eq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_3_eq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 2 → 32 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_3_eq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_3_eq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all

theorem dy'_month_3_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 2 → dt.Day.val < (if isleap then 29 else 28))
  (h1 : (if isleap then 60 else 59) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 90 else 89)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 59 else 58) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_3_eq dt isleap h h' h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_3_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_eq`. -/
theorem dy'_month_4_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 91 else 90) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 120 else 119)
    : 4 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_4_eq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_4_eq dt true a  (by simp; omega) (by simp; omega)]

/-- Generated by `gen_dy'_month_day_eq`. -/
theorem dy'_month_4_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 91 else 90) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 120 else 119)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 90 else 89) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_4_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_4_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_if_lt`. -/
theorem month_4_if_lt {dt : Date} (isLeap : Bool)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hl : isLeapYear dt.Year = isLeap)
    : dt.Month.val = 4 → dt.Day.val < 30 := by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := @month_4_if_eq ml.val isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all

/-- Generated by `gen_dy'_month_eq'`. -/
theorem dy'_month_5_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 4 → dt.Day.val < 30)
  (h1 : (if isleap then 121 else 120) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 151 else 150)
    : 5 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · have h' : a.val.fst = 4 → 91 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_5_eq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_5_eq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 4 → 92 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_5_eq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_5_eq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all

/-- Generated by `gen_dy'_month_day_eq'`. -/
theorem dy'_month_5_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 4 → dt.Day.val < 30)
  (h1 : (if isleap then 121 else 120) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 151 else 150)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 120 else 119) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_5_eq dt isleap h h' h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_5_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_eq`. -/
theorem dy'_month_6_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 152 else 151) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 181 else 180)
    : 6 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_6_eq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_6_eq dt true a  (by simp; omega) (by simp; omega)]

/-- Generated by `gen_dy'_month_day_eq`. -/
theorem dy'_month_6_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 152 else 151) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 181 else 180)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 151 else 150) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_6_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_6_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_if_lt`. -/
theorem month_6_if_lt {dt : Date} (isLeap : Bool)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hl : isLeapYear dt.Year = isLeap)
    : dt.Month.val = 6 → dt.Day.val < 30 := by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := @month_6_if_eq ml.val isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all

/-- Generated by `gen_dy'_month_eq'`. -/
theorem dy'_month_7_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 6 → dt.Day.val < 30)
  (h1 : (if isleap then 182 else 181) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 212 else 211)
    : 7 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · have h' : a.val.fst = 6 → 152 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_7_eq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_7_eq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 6 → 153 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_7_eq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_7_eq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all

/-- Generated by `gen_dy'_month_day_eq'`. -/
theorem dy'_month_7_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 6 → dt.Day.val < 30)
  (h1 : (if isleap then 182 else 181) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 212 else 211)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 181 else 180) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_7_eq dt isleap h h' h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_7_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_eq`. -/
theorem dy'_month_8_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 213 else 212) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 243 else 242)
    : 8 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_8_eq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_8_eq dt true a  (by simp; omega) (by simp; omega)]

/-- Generated by `gen_dy'_month_day_eq`. -/
theorem dy'_month_8_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 213 else 212) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 243 else 242)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 212 else 211) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_8_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_8_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_eq`. -/
theorem dy'_month_9_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 244 else 243) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 273 else 272)
    : 9 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_9_eq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_9_eq dt true a  (by simp; omega) (by simp; omega)]

/-- Generated by `gen_dy'_month_day_eq`. -/
theorem dy'_month_9_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 244 else 243) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 273 else 272)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 243 else 242) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_9_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_9_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_if_lt`. -/
theorem month_9_if_lt {dt : Date} (isLeap : Bool)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hl : isLeapYear dt.Year = isLeap)
    : dt.Month.val = 9 → dt.Day.val < 30 := by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := @month_9_if_eq ml.val isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all

/-- Generated by `gen_dy'_month_eq'`. -/
theorem dy'_month_10_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 9 → dt.Day.val < 30)
  (h1 : (if isleap then 274 else 273) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 304 else 303)
    : 10 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · have h' : a.val.fst = 9 → 244 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_10_eq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_10_eq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 9 → 245 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_10_eq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_10_eq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all

/-- Generated by `gen_dy'_month_day_eq'`. -/
theorem dy'_month_10_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 9 → dt.Day.val < 30)
  (h1 : (if isleap then 274 else 273) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 304 else 303)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 273 else 272) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_10_eq dt isleap h h' h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_10_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

/-- Generated by `gen_dy'_month_eq`. -/
theorem dy'_month_11_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 305 else 304) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 334 else 333)
    : 11 = dt.Month.val := by
  simp [dy'] at h1
  simp [dy'] at h2
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  rw [← this] at h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · simp_all [monthLastDayAsDayOfYear'_month_11_eq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayAsDayOfYear'_month_11_eq dt true a  (by simp; omega) (by simp; omega)]

/-- Generated by `gen_dy'_month_day_eq`. -/
theorem dy'_month_11_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h1 : (if isleap then 305 else 304) < dy' isleap dt.Month dt.Day + 1)
  (h2 : dy' isleap dt.Month dt.Day ≤ if isleap then 334 else 333)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 304 else 303) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_11_eq dt isleap h h1 h2
  have := monthLastDayAsDayOfYear'_day_of_month_11_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega

theorem month_11_if_lt {dt : Date} (isLeap : Bool)
  {ml : { m // monthLengthsOfDate m dt }}
  (hml : ml = monthLengths_of_date dt) (h : dt.Day.val < ml.val.snd)
  (hl : isLeapYear dt.Year = isLeap)
    : dt.Month.val = 11 → dt.Day.val < 30 := by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := @month_11_if_eq ml.val isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all

theorem dy'_month_12_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 11 → dt.Day.val < 30)
  (h1 : (if isleap then 335 else 334) < dy' isleap dt.Month dt.Day + 1)
    : 12 = dt.Month.val := by
  simp [dy'] at h1
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this] at h1
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1
  · have h' : a.val.fst = 11 → 305 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_12_eq' dt false a  (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_12_eq dt false a (h' h''.symm)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 11 → 306 < a.val.snd.fst := by omega
    have := monthLastDayAsDayOfYear'_month_12_eq' dt true a  (by simp; omega)
    cases this
    · rename_i h''
      have := monthLastDayAsDayOfYear'_month_12_eq dt true a (h' h''.symm)
      simp_all only [Bool.false_eq_true]
    · simp_all

theorem dy'_month_12_day_eq (dt : Date) (isleap : Bool)
  (h : dt.Day.val < 31)
  (h' : dt.Month.val = 11 → dt.Day.val < 30)
  (h1 : (if isleap then 335 else 334) < dy' isleap dt.Month dt.Day + 1)
    : dt.Day.val + 1 = dy' isleap dt.Month dt.Day - (if isleap then 334 else 333) := by
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'_month_12_eq dt isleap h h' h1
  have := monthLastDayAsDayOfYear'_day_of_month_12_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega
