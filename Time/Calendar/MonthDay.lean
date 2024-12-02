import Init.Data.Int.Order
import Batteries.Data.List.Lemmas
import Time.Data.Int.Order
import Time.Calendar.OrdinalDate
import Time.Data.List.Basic

namespace Time

open Clip

/-- Month and days of month. -/
def monthLengths (isleap : Bool) :=
  [ (1, 31), (2, if isleap then 29 else 28), (3, 31), (4, 30), (5, 31),
    (6, 30), (7, 31), (8, 31), (9, 30), (10, 31), (11, 30), (12, 31)]

/--  Date in proleptic Gregorian calendar. -/
@[ext] structure Date where
  Year : Int
  Month : Time.Icc 1 12
  Day : Time.Icc 1 31
  IsValid : ∃ m ∈ monthLengths (isLeapYear Year), m.1 = Month.val ∧ Day.val ≤ m.2
  deriving Repr

namespace Notation

/-- Date syntactic category -/
declare_syntax_cat date
/-- Date from numeric literals year, month and day -/
syntax num noWs "-" noWs num noWs "-" noWs num : date
syntax "date%" date : term

/--
  `date% year-month-day` is notation for
  `Time.Date.mk year ⟨month, by omega⟩ ⟨day, by omega⟩ (by native_decide)`
  for the numeric literals year, month and day.
-/
macro_rules
| `(date% $y:num-$m:num-$d:num) =>
    `(Time.Date.mk $y ⟨$m, by omega⟩ ⟨$d, by omega⟩ (by native_decide))

end Notation

instance : BEq Date where
  beq a b := decide (Eq a.Year b.Year) && decide (Eq a.Month.val b.Month.val) && decide (Eq a.Day.val b.Day.val)

instance : Inhabited Date where
  default := date% 1-1-1

/-- Last day of month as day of year, see `monthLengths_sum_le_map_pair`. -/
def monthLastDayAsDayOfYear (isleap : Bool) :=
  if isleap then [(1, 31), (2, 60), (3, 91), (4, 121), (5, 152), (6, 182),
                  (7, 213), (8, 244), (9, 274), (10, 305), (11, 335), (12, 366)]
  else [(1, 31), (2, 59), (3, 90), (4, 120), (5, 151), (6, 181),
        (7, 212), (8, 243), (9, 273), (10, 304), (11, 334), (12, 365)]

/-- First and last day of month as day of year, see `monthLengths_sum_le_map_pair'`. -/
def monthLastDayAsDayOfYear' (isleap : Bool) :=
  if isleap then [(1, 1, 31), (2, 32, 60), (3, 61, 91), (4, 92, 121), (5, 122, 152), (6, 153, 182),
      (7, 183, 213), (8, 214, 244), (9, 245, 274), (10, 275, 305), (11, 306, 335), (12, 336, 366)]
  else [(1, 1, 31), (2, 32, 59), (3, 60, 90), (4, 91, 120), (5, 121, 151), (6, 152, 181),
      (7, 182, 212), (8, 213, 243), (9, 244, 273), (10, 274, 304), (11, 305, 334), (12, 335, 365)]

@[simp] theorem monthLastDayAsDayOfYear_length_eq_12 (isleap : Bool)
    : (monthLastDayAsDayOfYear isleap).length = 12 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear_index_lt (i : Fin (monthLastDayAsDayOfYear isleap).length)
    :  i - 1 < (monthLastDayAsDayOfYear isleap).length := by
  cases isleap <;> simp_all [monthLastDayAsDayOfYear_length_eq_12]
  · have := monthLastDayAsDayOfYear_length_eq_12 false; omega
  · have := monthLastDayAsDayOfYear_length_eq_12 true; omega

@[simp] theorem monthLastDayAsDayOfYear'_length_eq_12 (isleap : Bool)
    : (monthLastDayAsDayOfYear' isleap).length = 12 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_index_lt (i : Fin (monthLastDayAsDayOfYear' isleap).length)
    :  i - 1 < (monthLastDayAsDayOfYear' isleap).length := by
  cases isleap <;> simp_all [monthLastDayAsDayOfYear'_length_eq_12]
  · have := monthLastDayAsDayOfYear'_length_eq_12 false; omega
  · have := monthLastDayAsDayOfYear'_length_eq_12 true; omega

theorem monthLastDayAsDayOfYear_sub_pred_le (isleap : Bool)
  : ∀ i : Fin (monthLastDayAsDayOfYear isleap).length,
    ((monthLastDayAsDayOfYear isleap).get i).2
      - ((monthLastDayAsDayOfYear isleap).get ⟨i-1, monthLastDayAsDayOfYear_index_lt i⟩).2
      ≤ 31 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_day_1_le (isleap : Bool)
  : ∀ a ∈ monthLastDayAsDayOfYear' isleap, 1 ≤ a.2.1 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_le_day_1 (isleap : Bool)
  : ∀ a ∈ monthLastDayAsDayOfYear' isleap, a.2.1 ≤ if isleap then 336 else 335 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_sub_pred_le (isleap : Bool)
  : ∀ i : Fin (monthLastDayAsDayOfYear' isleap).length,
    ((monthLastDayAsDayOfYear' isleap).get i).2.1 = if i.val = 0 then 1 else
      ((monthLastDayAsDayOfYear' isleap).get ⟨i-1, monthLastDayAsDayOfYear'_index_lt i⟩).2.2+1 := by
  cases isleap <;> simp_arith

theorem monthLastDayAsDayOfYear'_sub_days_le (isleap : Bool)
  : ∀ i : Fin (monthLastDayAsDayOfYear' isleap).length,
    ((monthLastDayAsDayOfYear' isleap).get i).2.2
    - ((monthLastDayAsDayOfYear' isleap).get i).2.1 ≤ 30 := by
  cases isleap <;> simp_arith

theorem Int.le_of_sub_le {a b c d : Nat} (h1 : a ≤ c) (h2 : c - b ≤ d)
    : a - b ≤ d := by
  omega

theorem monthLastDayAsDayOfYear'_val_in (isLeap : Bool) (yd : Nat)
  (i : Fin (monthLastDayAsDayOfYear' isLeap).length)
  (h2 : yd ≤ (monthLastDayAsDayOfYear' isLeap)[i].2.2)
  : 1 ≤ yd - (monthLastDayAsDayOfYear' isLeap)[i].2.1 + 1 ∧
    yd - (monthLastDayAsDayOfYear' isLeap)[i].2.1 + 1 ≤ 31 := by
  have hle := monthLastDayAsDayOfYear'_sub_days_le isLeap i
  simp_arith
  exact Int.le_of_sub_le h2 hle

theorem monthLastDayAsDayOfYear_val_le (isleap : Bool)
  (i : Fin (monthLastDayAsDayOfYear isleap).length) (val : Nat)
  (hVal : val = ((monthLastDayAsDayOfYear isleap).get ⟨i-1, monthLastDayAsDayOfYear_index_lt i⟩).2)
  (h1 : ¬yd ≤ val) (h2 : yd ≤ ((monthLastDayAsDayOfYear isleap).get i).2)
    : 1 ≤ yd - val ∧ yd - val ≤ 31 := by
  have : val < yd := by simp_all [h1]
  have hLeft : 1 ≤ yd - val := by
    omega
  have hRight : yd - val ≤ 31 := by
    have := monthLastDayAsDayOfYear_sub_pred_le isleap i
    rw [← hVal] at this
    omega
  simp_all

/-- Sum of month lengths upto month `m` -/
def monthLengths_sum_le (isleap : Bool) (m : Nat) : Nat :=
  monthLengths isleap
  |> List.takeWhile (fun ml => ml.1 ≤ m)
  |> List.foldl (fun acc ml => ml.2 + acc) 0

def monthLengths_sum_le_map (isleap : Bool) : List Nat :=
  monthLengths isleap |> List.map (monthLengths_sum_le isleap ·.1)

def monthLengths_sum_le_map_pair (isleap : Bool) : List (Nat × Nat) :=
  monthLengths isleap |> List.map (fun ml => (ml.1, monthLengths_sum_le isleap ml.1))

def monthLengths_sum_le_map_pair' (isleap : Bool)  :=
  monthLengths isleap |> List.map (fun ml => (ml.1, monthLengths_sum_le isleap ml.1))
  |> fun l => List.zip ([(0, 0)] ++ l) l
  |> List.map (fun (x, y) => (y.1, (x.2+1, y.2)))

theorem monthLengths_sum_le_eq_monthLastDayAsDayOfYear (isleap : Bool)
    : monthLengths_sum_le_map isleap
    = (monthLastDayAsDayOfYear isleap |> List.map (fun x => x.2)) := by
  cases isleap <;> simp_arith

def monthLengths' (isleap : Bool) :=
  (monthLengths isleap).lookup

def monthLengths_sum (isleap : Bool) : Nat :=
  (monthLengths isleap).foldl (fun acc m => acc + m.2) 0

theorem monthLengths_sum_eq (isleap : Bool) :
  monthLengths_sum isleap == if isleap then 366 else 365 := by
  cases isleap <;> simp_arith

theorem monthLengths_length_eq_12 (isleap : Bool) : (monthLengths isleap).length == 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_length_gt_0 (isleap : Bool) : 0 < (monthLengths isleap).length := by
  cases isleap <;> simp_arith

theorem monthLengths_month_in (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.1 ∧ a.1 ≤ 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_in (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.2 ∧ a.2 ≤ 31 := by
  cases isleap <;> simp_arith

theorem list_foldl_init_add (l : List α) (init v : Nat) (f : α → Nat)
  : List.foldl (fun acc v => f v + acc) init l + v
    = List.foldl (fun acc v => f v + acc) (init + v) l := by
  induction l generalizing init with
  | nil =>
    unfold List.foldl
    simp_all
  | cons h t ih =>
    unfold List.foldl
    simp [*]
    have hy : List.foldl (fun acc v => f v + acc) ((f h + init) + v) t
              = List.foldl (fun acc v => f v + acc) (f h + (init + v)) t := by
      have : (f h + init) + v = f h + (init + v) := by simp_arith
      rw [this]
    rw [hy]

def findValidMonthDay_1 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨0, by simp⟩).2) : Date :=
  ⟨year, ⟨1, by simp⟩, ⟨yd.val, And.intro (by simp_all [yd.property])
      (by simp [monthLastDayAsDayOfYear] at h; cases isLeap <;> exact h)⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths]; cases isLeap <;> exact h⟩

def findValidMonthDay_2 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[0].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨1, by simp⟩).2) : Date :=
  ⟨year, ⟨2, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[0].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨1, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[0].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_3 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[1].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨2, by simp⟩).2) : Date :=
  ⟨year, ⟨3, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[1].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨2, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[1].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_4 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[2].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨3, by simp⟩).2) : Date :=
  ⟨year, ⟨4, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[2].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨3, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[2].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_5 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[3].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨4, by simp⟩).2) : Date :=
  ⟨year, ⟨5, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[3].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨4, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[3].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_6 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[4].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨5, by simp⟩).2) : Date :=
  ⟨year, ⟨6, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[4].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨5, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[4].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_7 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[5].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨6, by simp⟩).2) : Date :=
  ⟨year, ⟨7, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[5].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨6, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[5].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_8 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[6].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨7, by simp⟩).2) : Date :=
  ⟨year, ⟨8, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[6].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨7, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[6].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_9 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[7].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨8, by simp⟩).2) : Date :=
  ⟨year, ⟨9, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[7].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨8, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[7].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_10 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[8].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨9, by simp⟩).2) : Date :=
  ⟨year, ⟨10, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[8].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨9, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[8].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_11 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[9].snd)
  (h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨10, by simp⟩).2) : Date :=
  ⟨year, ⟨11, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[9].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨10, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[9].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_12 (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap)
  (hn : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[10].snd)
  (hle : yd.val ≤ if isLeap then 366 else 365) : Date :=
  have h : yd.val ≤ ((monthLastDayAsDayOfYear isLeap).get ⟨11, by simp⟩).2 := by
    simp [monthLastDayAsDayOfYear]; cases isLeap <;> simp_all
  ⟨year, ⟨12, by simp⟩, ⟨yd.val - (monthLastDayAsDayOfYear isLeap)[10].2,
    by exact monthLastDayAsDayOfYear_val_le isLeap ⟨11, by simp_all⟩
        ((monthLastDayAsDayOfYear isLeap)[10].snd) (by simp) hn h⟩,
    by simp [monthLastDayAsDayOfYear] at h; simp_all [monthLengths];
        cases isLeap <;> simp [monthLastDayAsDayOfYear] <;> simp [] at h <;> omega⟩

def findValidMonthDay_tail (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap) (hle : yd.val ≤ if isLeap then 366 else 365)
  (h6 : ¬yd.val ≤ (monthLastDayAsDayOfYear isLeap)[5].snd)
    : Date :=
  if h7 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[6].2
  then findValidMonthDay_7 year isLeap yd hl h6 h7
  else if h8 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[7].2
  then findValidMonthDay_8 year isLeap yd hl h7 h8
  else if h9 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[8].2
  then findValidMonthDay_9 year isLeap yd hl h8 h9
  else if h10 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[9].2
  then findValidMonthDay_10 year isLeap yd hl h9 h10
  else if h11 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[10].2
  then findValidMonthDay_11 year isLeap yd hl h10 h11
  else findValidMonthDay_12 year isLeap yd hl h11 hle

def findValidMonthDay (year : Int) (isLeap : Bool) (yd : Time.Icc 1 366)
  (hl : isLeapYear year = isLeap) (hle : yd.val ≤ if isLeap then 366 else 365)
    : Date :=
  if h1 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[0].2
  then findValidMonthDay_1 year isLeap yd h1
  else if h2 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[1].2
  then findValidMonthDay_2 year isLeap yd hl h1 h2
  else if h3 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[2].2
  then findValidMonthDay_3 year isLeap yd hl h2 h3
  else if h4 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[3].2
  then findValidMonthDay_4 year isLeap yd hl h3 h4
  else if h5 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[4].2
  then findValidMonthDay_5 year isLeap yd hl h4 h5
  else if h6 : yd.val ≤ (monthLastDayAsDayOfYear isLeap)[5].2
  then findValidMonthDay_6 year isLeap yd hl h5 h6
  else findValidMonthDay_tail year isLeap yd hl hle h6

theorem isLeapYear_false {dt : OrdinalDate} (h : dt.dayOfYear = DayOfYear.common yd)
    : isLeapYear dt.year = false := by
  have h := dt.isValid
  split at h <;> simp_all

theorem isLeapYear_true {dt : OrdinalDate} (h : dt.dayOfYear = DayOfYear.leap yd)
    : isLeapYear dt.year = true := by
  have h := dt.isValid
  split at h <;> simp_all

def ordinalDateToDate (dt : OrdinalDate) : Date :=
  match h : dt.dayOfYear with
  | .common yd => findValidMonthDay dt.year false yd (isLeapYear_false h)
                    (by split <;> simp_all [yd.property.right])
  | .leap yd => findValidMonthDay dt.year true yd (isLeapYear_true h)
                    (by split <;> simp_all [yd.property.right])

theorem monthLengths_month_le_12 (isleap : Bool)
  : ∀ a ∈ (monthLengths isleap), 1 ≤ a.1 ∧ a.1 ≤ 12 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_ge_28 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), 28 <= a.2 := by
  cases isleap <;> simp_arith

theorem monthLengths_days_le_31 (isleap : Bool) : ∀ a ∈ (monthLengths isleap), a.2 <= 31 := by
  cases isleap <;> simp_arith

/-- The length of a given month in the Gregorian or Julian calendars. -/
def monthLength' (isLeap : Bool) (month': Fin 12) :=
  ((monthLengths isLeap).get month').2

theorem monthLength'_ge_1 (isLeap : Bool) (month': Fin 12)
   : 1 <= monthLength' (isLeap : Bool) (month': Fin 12) := by
  simp only [monthLength']
  have h1 : 1 ≤ 28 := by omega
  have h : List.get (monthLengths _) _ ∈ monthLengths _ :=
    List.get_mem (monthLengths isLeap) month'.val month'.isLt
  have h2: 28 <= monthLength' _ _ := monthLengths_days_ge_28 _ _ h
  exact Nat.le_trans h1 h2

theorem monthLength'_le_31 (isLeap : Bool) (month': Fin 12)
   : monthLength' (isLeap : Bool) (month': Fin 12) <= 31 := by
  simp only [monthLength']
  have h : List.get (monthLengths _) _ ∈ monthLengths _ :=
    List.get_mem (monthLengths isLeap) month'.val month'.isLt
  exact monthLengths_days_le_31 _ _ h

theorem monthAndDayToDayOfYear_gt_zero_of_month_gt (month day k : Int)
    (hm : 2 < month) (hk : -2 ≤ k) (hd : 0 < day)
    : 0 < ((367 * month - 362) / 12 + k) + day := by
  let y := 367 * month - 362

  have ha : 0 ≤ y / 12 + k := by
    have h1 : 0 <= 2 + k := Int.add_le_add_left hk _
    have h2 : 2 + k <= y / 12 + k := by omega
    simp [Int.le_trans h1 h2]

  simp [Int.add_pos_of_nonneg_of_pos ha hd]

theorem exists_month_in_monthLastDayAsDayOfYear' (isleap : Bool) (month : Icc 1 12)
     : ∃ m ∈ monthLastDayAsDayOfYear' isleap, m.1 = month.val := by
  have := month.property
  cases isleap <;> simp [monthLastDayAsDayOfYear'] <;> omega

theorem exists_days_in_monthLastDayAsDayOfYear' (isleap : Bool) (month : Icc 1 12)
     : ∃ a b, (month.val, a, b) ∈ monthLastDayAsDayOfYear' isleap := by
  have ⟨m, h⟩ := exists_month_in_monthLastDayAsDayOfYear' isleap month
  exact ⟨m.2.1, by exact ⟨m.2.2, by rw [← h.right]; simp [h.left]⟩⟩

def memOfMonth (isleap : Bool) (month : Icc 1 12)
    : { x // x ∈ monthLastDayAsDayOfYear' isleap ∧ x.fst = month } :=
  let a := List.findExisting
    (fun (m : Nat × Nat × Nat) => m.fst = month) (monthLastDayAsDayOfYear' isleap)
    (by simp; exact exists_days_in_monthLastDayAsDayOfYear' isleap month)
  ⟨a.val, by
    have := a.property.right
    simp_all
    exact a.property.left⟩

/-- Get day of year from month and day of month by lookup in `monthLastDayAsDayOfYear'`. -/
def dy' (isleap : Bool) (month : Icc 1 12) (day : Icc 1 31) :=
  (memOfMonth isleap month).val.2.1 + day - 1

theorem le_dy' (isleap : Bool) (month : Icc 1 12) (day : Icc 1 31)
    : 1 ≤ (dy' isleap month day) := by
  simp [dy']
  have := day.property
  have := monthLastDayAsDayOfYear'_day_1_le isleap
            (memOfMonth isleap month).1
            (memOfMonth isleap month).property.left
  omega

theorem dy'_le (isleap : Bool) (month : Icc 1 12) (day : Icc 1 31)
    : (dy' isleap month day) ≤ if isleap then 366 else 365 := by
  simp [dy']
  have := day.property
  have := monthLastDayAsDayOfYear'_le_day_1 isleap
            (memOfMonth isleap month).1
            (memOfMonth isleap month).property.left
  split
  · split at this <;> omega
  · split at this
    · contradiction
    · omega

/-- Compute day of year from month (1..12) and day of month (1..31).  -/
def dy (isleap : Bool) (month day : Nat) :=
  let k : Int := if month ≤ 2 then 0 else if isleap then -1 else -2
  ((367 * month - 362) / 12 + k + day).toNat

/-- The day of year of the last day of a month can be computed as the predecessor
    of the first day of the next month. -/
def dyOfLastDayOfMonth (isleap : Bool) (month : Nat) :=
  dy isleap (month + 1) 0

theorem le_dy (isleap : Bool) (month : Icc 1 12) (day : Icc 1 31)
    : 1 ≤ (dy isleap month day) := by
  have := month.property
  have := day.property
  simp [dy]
  split <;> try simp_all
  · have hle : (1:Int) ≤ ((367 * month - 362) / 12 + day : Int) := by omega
    have := Int.toNat_le_toNat hle
    exact this
  · split <;> try simp_all
    · have hle : (1:Int) ≤ ((367 * month - 362) / 12 - 1 + day : Int) := by omega
      have := Int.toNat_le_toNat hle
      exact this
    · have hle : (1:Int) ≤ ((367 * month - 362) / 12 - 2 + day : Int) := by omega
      have := Int.toNat_le_toNat hle
      exact this

theorem dy_le (isleap : Bool) (month : Icc 1 12) (day : Icc 1 31)
    : (dy isleap month day) ≤ if isleap then 366 else 365 := by
  have := month.property
  have := day.property
  simp [dy]
  split <;> try simp_all
  · have hle' : 70 ≤ if isleap then 366 else 365 := by split <;> omega
    have hle : ((367 * month - 362) / 12 + day : Int) ≤ if isleap then 366 else 365 := by omega
    have hle := Int.toNat_le_toNat hle
    have : (if isleap = true then 366 else 365 : Int).toNat
         = if isleap = true then 366 else 365 := by cases isleap <;> simp_all
    rw [this] at hle
    exact hle
  · split <;> try simp_all
    · have hle : ((367 * month - 362) / 12 - 1 + day : Int) ≤ 366 := by omega
      have := Int.toNat_le_toNat hle
      exact this
    · have hle : ((367 * month - 362) / 12 - 2 + day : Int) ≤ 365 := by omega
      have := Int.toNat_le_toNat hle
      exact this

def monthAndDayToDayOfYearClipped' (year : Int) (month day : Nat)
    (hd1 : 1 <= day) (hd2 : day ≤ 31) (hm1 : 1 ≤ month) (hm2 : month <= 12) : OrdinalDate :=
  let month : Icc 1 12 := ⟨month, And.intro hm1 hm2⟩
  let day : Icc 1 31 := ⟨day, And.intro hd1 hd2⟩
  if h : isLeapYear year
  then
    let dayOfYear : DayOfYear := .leap ⟨(dy true month day), And.intro
          (le_dy true month day)
          (by exact dy_le true month day)⟩
    ⟨year, dayOfYear, by simp [dy, h]⟩
  else
    let dy : DayOfYear := .common ⟨(dy false month day), And.intro
          (le_dy false month day)
          (by exact dy_le false month day)⟩
    ⟨year, dy, by simp [dy, h]⟩

def monthAndDayToDayOfYearClipped (year : Int) (month' : NonemptyIcc 1 12)
    (day' : Nat) (hd1 : 1 <= day') (hd2 : day' ≤ 31) : OrdinalDate :=
  monthAndDayToDayOfYearClipped' year month'.icc.val day' hd1 hd2
    month'.icc.property.left month'.icc.property.right

theorem days_le_31 (isLeap : Bool) (m : Fin 12) (day : NonemptyIcc 1 (monthLength' isLeap m))
    : day.icc.val ≤ 31 :=
  have h1 : day.icc.val ≤  monthLength' isLeap m := day.icc.property.right
  have h2 : monthLength' isLeap m ≤ 31 := monthLength'_le_31 isLeap m
  Nat.le_trans h1 h2

/-- Convert month and day in the Gregorian or Julian calendars to day of year. -/
def monthAndDayToDayOfYear (year : Int) (month : Int) (day : Int) : OrdinalDate :=
  let month' := clipToNonemptyIcc 1 12 month (by simp_arith)
  let month'' : Fin 12 := month'
  let isLeap := isLeapYear year
  let day' := clipToNonemptyIcc 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  monthAndDayToDayOfYearClipped year month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')

/-- Convert month and day in the Gregorian or Julian calendars to day of year option. -/
def monthAndDayToDayOfYearValid (year : Int) (month : Int) (day : Int)
    : Option  $ OrdinalDate := do
  let month' ← clipToNonemptyIcc? 1 12 month (by simp_arith)
  let month'' : Fin 12 :=  month'
  let isLeap := isLeapYear year
  let day' ← clipToNonemptyIcc? 1 (monthLength' isLeap month'') day (monthLength'_ge_1 isLeap month'')

  return monthAndDayToDayOfYearClipped year month' day'.icc.val day'.icc.property.left
    (days_le_31 isLeap month'' day')

def dateToOrdinalDate (dt : Date) : OrdinalDate :=
  if h : isLeapYear dt.Year
  then
    let dayOfYear : DayOfYear := .leap ⟨(dy true dt.Month dt.Day), And.intro
          (le_dy true dt.Month dt.Day)
          (by exact dy_le true dt.Month dt.Day)⟩
    ⟨dt.Year, dayOfYear, by simp [dy, h]⟩
  else
    let dy : DayOfYear := .common ⟨(dy false dt.Month dt.Day), And.intro
          (le_dy false dt.Month dt.Day)
          (by exact dy_le false dt.Month dt.Day)⟩
    ⟨dt.Year, dy, by simp [dy, h]⟩
