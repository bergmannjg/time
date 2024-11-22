import Time
import Time.Verify

namespace Playgroud

open Time
open Time.Notation
open Verify.OrdinalDate

def Icc.dayOfYear (dt : OrdinalDate) : Icc 1 366 :=
  ⟨Time.dayOfYear dt.dayOfYear, by
    unfold Time.dayOfYear
    split <;> try simp_all
    · rename_i a _; simp [a.property, Nat.le_succ_of_le]
    · rename_i a _; simp [a.property]⟩

def a (dt: OrdinalDate) :=
  let a := Icc.dayOfYear dt
  (a.val + 365 * (dt.year - 1) + (dt.year - 1) / 4 - (dt.year - 1) / 100
    + (dt.year - 1) / 400
    + -678576 + 678575)

def quadcent (dt: OrdinalDate) :=
  (a dt) / 146097

def cent (dt: OrdinalDate) :=
  let b := (a dt) % 146097
  if b = 146096 then 3 else b / 36524

def c (dt: OrdinalDate) :=
  let b := (a dt) % 146097
  b - ((cent dt) * 36524)

def quad (dt: OrdinalDate) :=
  (c dt) / 1461

def d' (dt: OrdinalDate) :=
    (c dt) % 1461

def birthday := date% 1954-07-26
def dy := monthAndDayToDayOfYear (isLeapYear birthday.Year) birthday.Month.val birthday.Day.val

def dt : OrdinalDate := {
  year := 1
  dayOfYear := .common ⟨2, by simp_all⟩
  isValid := by split <;> simp_all [isLeapYear]}

#eval (dt.year-1) / 400 * 400 + (dt.year - (dt.year - 1) / 400 * 400) / 100 * 100
#eval isLeapYear 1900
#eval 146096 / 36524
#eval (fromOrdinalDate dt).modifiedJulianDay + 678575
#eval toGregorian (fromOrdinalDate dt)
#eval days_since_1_1_1 dt (Icc.dayOfYear dt)
#eval (a dt)
#eval (a dt) % 146097
#eval quadcent dt
#eval cent dt
#eval quad dt
#eval d' dt

#eval Verify.OrdinalDate.days_since_1_1_1_mod_146097_mod_36524 dt (Icc.dayOfYear dt)
#eval Verify.OrdinalDate.quadcent dt
#eval Verify.OrdinalDate.cent dt
#eval Verify.OrdinalDate.quad dt
#eval Verify.OrdinalDate.d' dt (Icc.dayOfYear dt)

#eval Verify.OrdinalDate.c dt (Icc.dayOfYear dt)
#eval Verify.OrdinalDate.c_value dt (Icc.dayOfYear dt)

#eval Verify.OrdinalDate.c_value dt (Icc.dayOfYear dt) / 1461

#eval (quadcent dt) * 400
      + (cent dt) * 100
      + (quad dt) * 4
      + (d' dt) / 365
      + 1

-- 146097
-- 4*(76*365+24*366) + 1
-- 304*365+96*366 + 1

-- 304*365+96*365 + 96 + 1

def y' := dt.year-1 - 400


#eval (dt.year-1) / 4
#eval (dt.year-1) / 100
#eval (dt.year-1) / 400
#eval (dt.year-1) % 400
#eval ((dt.year-1) / 400) * 400 + (dt.year-1) % 400

#eval  365 * (400 - (dt.year-1) % 400)
#eval  (dt.year-1) / 4 - ((dt.year-1) / 400) * 96 - (dt.year-1) / 100

#eval toOrdinalDate (fromOrdinalDate dt)

#eval (dt.year-1) - 1
#eval (dt.year - 1) / 4 - (dt.year - 1) / 400 * 96 - (dt.year - 1) / 100
#eval ((dt.year-1) / 400) * 400
#eval ((dt.year-1) % 400)
#eval ((dt.year-1) / 400)
#eval ((dt.year-1) / 4)

#eval (dt.year-1) - 1 - ((dt.year-1) / 400) * 400

#eval (dt.year-1) % 400
#eval ((dt.year-1) / 400) * 400 + (dt.year-1) % 400

def toModifiedJulianDay_year_rest (dt : OrdinalDate) :=
 let a := Icc.dayOfYear dt
 (365 * ((dt.year-1)-((dt.year-1) / 400)*400))
        + ((dt.year-1) / 4) - (((dt.year-1) / 400)*96)
        - ((dt.year-1) / 100) - 1 + a.val

#eval (toModifiedJulianDay_year_rest dt) / 1461
#eval ((toModifiedJulianDay_year_rest dt) % 146097) / 36524
#eval 1462 - 1096

def loop (n : Nat) (jd : Int) : IO PUnit := do
  let dt : OrdinalDate := Time.toOrdinalDate ⟨jd⟩
  let a := Icc.dayOfYear dt
  if n = 0 then IO.println s!"finished {dt}"
  else
    let q1 := days_since_1_1_1_mod_146097'' dt ⟨1, by simp⟩ + a.val - 1
    let q2 := days_since_1_1_1_mod_146097'' dt a
    if q1 != q2
      then
      IO.println s!"found year {dt} q1 {q1} q2 {q2}"
      loop (n-1) (jd + 1)
    else
      loop (n-1) (jd + 1)

-- january 1, year 1 = 678575
#eval loop 800000 (-978575)

#eval days_since_1_1_1_mod_146097 dt dy / 36524

#eval (dt.year - 4*400)

#eval (dt.year - 1) / 400

#eval (dt.year - 1) / 400 * 400 + (dt.year - (dt.year - 1) / 400 * 400) / 100 * 100

#eval days_since_1_1_1_mod_146097_mod_36524 dt (Icc.dayOfYear dt) % 36524
#eval Icc.dayOfYear dt
#eval days_since_1_1_1_mod_146097_mod_36524 dt (Icc.dayOfYear dt)
