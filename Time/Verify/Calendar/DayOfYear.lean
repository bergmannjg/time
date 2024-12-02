import Time
import Time.Data.List.Basic
import Time.Verify.Calendar.MonthLength

/-!
## Theorems about `Time.dy'` properties

Main theorems:

* `Verify.DayOfYear.Notation.«termDy'MonthEq%_»`
* `Verify.DayOfYear.Notation.«termDy'MonthDayEq%_»`

-/

namespace Verify
namespace DayOfYear

open Time
open MonthLength

namespace Notation

declare_syntax_cat dy'MonthEq
syntax num ws num ws num ws num ws num ws num ws num : dy'MonthEq
syntax "dy'MonthEq%" dy'MonthEq : term

/-- proof of `$m = dt.Month.val` -/
macro_rules
| `(dy'MonthEq% $m:num $v:num $v':num $p:num $p':num $n:num $n':num) =>
    `((fun dt isleap a h1 h2 => by
  have monthLastDayMonthEq := monthLastDayMonthEq% $m:num $p $p' $n $n'
  simp [dy'] at h1
  simp [dy'] at h2
  generalize memOfMonth isleap dt.Month = a at h1 h2
  have := dt.Day.property
  have := a.property
  cases isleap <;> simp [] at h2 <;> try simp [] at h1
  · simp_all [monthLastDayMonthEq dt false a  (by simp; omega) (by simp; omega)]
  · simp_all [monthLastDayMonthEq dt true a  (by simp; omega) (by simp; omega)]
    : ∀ (dt : Date) (isleap : Bool),
    dt.Day.val < 31 →
    (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
    (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
    $m = dt.Month.val))

--#check dy'MonthEq% 4 91 90 61 60 120 119

declare_syntax_cat dy'MonthDayEq
syntax num ws num ws num ws num ws num ws num ws num  ws num ws num : dy'MonthDayEq
syntax "dy'MonthDayEq%" dy'MonthDayEq : term

/-- proof of `dt.Day.val + 1 = dy' ...` -/
macro_rules
| `(dy'MonthDayEq% $m:num $v:num $v':num $p:num $p':num $n:num $n':num $v1:num $v1':num) =>
    `((fun dt isleap h h1 h2 => by
  let dy'MonthEq := dy'MonthEq% $m:num $v $v' $p $p' $n $n'
  simp [dy']
  generalize memOfMonth isleap dt.Month = a
  have := dy'MonthEq dt isleap h h1 h2
  have := (monthLastDayMonthDayEq% $m:num $v1 $v1') dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega
    : ∀ (dt : Date) (isleap : Bool),
        dt.Day.val < 31 →
        (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
        (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
        dt.Day.val + 1 = dy' isleap dt.Month dt.Day - if isleap = true then ($v-1) else ($v'-1)))

--#check dy'MonthDayEq% 4 91 90 61 60 120 119 92 91

declare_syntax_cat dy'MonthEq'
syntax num ws num ws num ws num ws num ws num ws num ws num ws num ws num : dy'MonthEq'
syntax "dy'MonthEq'%" dy'MonthEq' : term

/-- proof of `$m = dt.Month.val` -/
macro_rules
| `(dy'MonthEq'% 3 $v:num $v':num $p:num $p':num $n:num $n':num $v1:num $v1':num 2) =>
    `((fun dt isleap h h' h1 h2 => by
  have monthEq := monthLastDayMonthEq% 3 $p $p' $n $n'
  have monthEq' := monthLastDayMonthEq'% 3 $v1 $v1' 31 30
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
    have := monthEq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthEq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = 2 → 32 < a.val.snd.fst := by omega
    have := monthEq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthEq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
    : ∀ (dt : Date) (isleap : Bool),
        dt.Day.val < 31 →
        (dt.Month.val = 2 → dt.Day.val < if isleap then 29 else 28) →
        (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
        (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
        3 = dt.Month.val))
| `(dy'MonthEq'% $m:num $v:num $v':num $p:num $p':num $n:num $n':num $v1:num $v1':num $m1:num) =>
    `((fun dt isleap h h' h1 h2 => by
  have monthEq := monthLastDayMonthEq% $m:num $p $p' $n $n'
  have monthEq' := monthLastDayMonthEq'% $m:num $v1 $v1' $p $p'
  simp [dy'] at h1
  simp [dy'] at h2
  generalize memOfMonth isleap dt.Month = a at h1 h2
  have := dt.Day.property
  have := a.property
  have hmem : a.val.fst = dt.Month.val := a.property.right
  rw [← hmem] at h'
  cases isleap <;> simp [] at h1 <;> simp [] at h2
  · have h' : a.val.fst = $m1 → $p' < a.val.snd.fst := by omega
    have := monthEq' dt false a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthEq dt false a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
  · have h' : a.val.fst = $m1 → $p < a.val.snd.fst := by omega
    have := monthEq' dt true a  (by simp; omega) (by simp; omega)
    cases this
    · rename_i h''
      have := monthEq dt true a (h' h''.symm) (by simp; omega)
      simp_all only [Bool.false_eq_true]
    · simp_all
    : ∀ (dt : Date) (isleap : Bool),
        dt.Day.val < 31 →
        (dt.Month.val = $m1 → dt.Day.val < 30) →
        (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
        (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
        $m:num = dt.Month.val))

--#check dy'MonthEq'% 5 121 120 92 91 151 150 152 151 4

--#check dy'MonthEq'% 3 60 59 32 32 90 89 91 90 2

declare_syntax_cat dy'MonthDayEq'
syntax num ws num ws num ws num ws num ws num ws num  ws num ws num ws num ws num ws num ws num : dy'MonthDayEq'
syntax "dy'MonthDayEq'%" dy'MonthDayEq' : term

/-- proof of `$m = dt.Month.val' ...` -/
macro_rules
| `(dy'MonthDayEq'% 3 $v:num $v':num $p:num $p':num $n:num $n':num
                    $v1:num $v1':num $v2:num $v2':num $v3:num 2) =>
    `((fun dt isleap h h' h1 h2 =>  by
  have dy'MonthEq' := dy'MonthEq'% 3 $v $v' $p $p' $n $n' $v1 $v1' 2
  simp [dy']
  let a := memOfMonth isleap dt.Month
  have : a = memOfMonth isleap dt.Month := by simp
  rw [← this]
  have := dy'MonthEq' dt isleap h h' h1 h2
  have monthLastDayMonthDayEq := (monthLastDayMonthDayEq% 3 $v3 $v) dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega
    : ∀ (dt : Date) (isleap : Bool),
        dt.Day.val < 31 →
        (dt.Month.val = 2 → dt.Day.val < if isleap then 29 else 28) →
        (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
        (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
        dt.Day.val + 1 = dy' isleap dt.Month dt.Day - if isleap = true then $v2 else $v2'))
| `(dy'MonthDayEq'% $m:num $v:num $v':num $p:num $p':num $n:num $n':num
                    $v1:num $v1':num $v2:num $v2':num $v3:num $m1:num) =>
    `((fun dt isleap h h' h1 h2 =>  by
  have dy'MonthEq' := dy'MonthEq'% $m:num $v $v' $p $p' $n $n' $v1 $v1' $m1
  simp [dy']
  generalize memOfMonth isleap dt.Month = a
  have := dy'MonthEq' dt isleap h h' h1 h2
  have monthLastDayMonthDayEq := (monthLastDayMonthDayEq% $m:num $v3 $v) dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega
    : ∀ (dt : Date) (isleap : Bool),
        dt.Day.val < 31 →
        (dt.Month.val = $m1 → dt.Day.val < 30) →
        (if isleap = true then $v else $v') < dy' isleap dt.Month dt.Day + 1 →
        (dy' isleap dt.Month dt.Day ≤ if isleap = true then $n else $n') →
        dt.Day.val + 1 = dy' isleap dt.Month dt.Day - if isleap = true then $v2 else $v2'))

--#check dy'MonthDayEq'% 5 121 120 92 91 151 150 152 151 120 119 122 4

--#check dy'MonthDayEq'% 3 60 59 32 32 90 89 91 90 59 58 61 2

declare_syntax_cat monthIfLt
syntax num : monthIfLt
syntax "monthIfLt%" monthIfLt : term

/-- proof of `dt.Day.val < 30` -/
macro_rules
| `(monthIfLt% 2) =>
    `((fun {dt} isLeap {ml} hml h hl => by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := (monthIfEq% 2) isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all
    : ∀ {dt : Date} (isLeap : Bool)
      {ml : { m // monthLengthsOfDate m dt }},
      ml = monthLengths_of_date dt →
      dt.Day.val < ml.val.snd →
      isLeapYear dt.Year = isLeap →
      dt.Month.val = 2 →
      dt.Day.val < if isLeap then 29 else 28))
| `(monthIfLt% $m:num) =>
    `((fun {dt} isLeap {ml} hml h hl => by
  have hp := ml.property
  simp [monthLengthsOfDate] at hp
  intro
  rename_i h
  rw [← hp.right.left] at h
  have hm := (monthIfEq% $m:num) isLeap (by have := ml.property.left; rwa [hl] at this)
  simp [monthLengths, h] at hm
  have := ml.property
  simp_all
    : ∀ {dt : Date} (isLeap : Bool)
      {ml : { m // monthLengthsOfDate m dt }},
      ml = monthLengths_of_date dt →
      dt.Day.val < ml.val.snd →
      isLeapYear dt.Year = isLeap →
      dt.Month.val = $m →
      dt.Day.val < 30))

--#check monthIfLt% 4

end Notation

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
  generalize memOfMonth isleap dt.Month = a at h1
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
  generalize memOfMonth isleap dt.Month = a
  have := dy'_month_12_eq dt isleap h h' h1
  have := monthLastDayAsDayOfYear'_day_of_month_12_eq dt isleap a (by omega)
  cases isleap <;> simp_all <;> omega
