import Time

open Time
open Time.Notation
open Lean Parsec Clip

/-- see https://heasarc.gsfc.nasa.gov/cgi-bin/Tools/xTime/xTime.pl-/

def dt_1858_11_17 : Date := date% 1858-11-17

def dt_1997_1_1 : Date := date% 1997-1-1

def dt_2023_2_3 : Date := date% 2023-2-3

example : fromGregorian default == (default : Day) := by rfl

example : fromGregorianClipped 0 12 31 == Day.addDays (-1)  (default : Day) := by rfl

example : fromGregorian dt_1858_11_17 == ⟨0⟩ := by rfl

example : fromGregorian dt_1997_1_1 == ⟨50449⟩ := by rfl

example : fromGregorianClipped 1997 1 1 == ⟨50449⟩ := by rfl

example : fromGregorianValid 1997 1 1 == some ⟨50449⟩ := by rfl

example : toGregorian ⟨50449⟩ == dt_1997_1_1 := by rfl

example : toGregorian (fromGregorian dt_2023_2_3) == dt_2023_2_3 := by rfl

example : toOrdinalDate default == ⟨1, .common ⟨1, by simp_arith⟩, (by simp_arith)⟩ := by rfl

example : toOrdinalDate ⟨0⟩  == ⟨1858, .common ⟨321, by simp_arith⟩, by simp_arith⟩ := by rfl

example : (toOrdinalDate <| fromOrdinalDate ⟨2023, .common ⟨50, by simp_arith⟩, (by simp_arith)⟩)
  == ⟨2023, .common ⟨50, by simp_arith⟩, (by simp_arith)⟩ := by rfl

def dt_2023_1_17 : Date := date% 2023-1-17

example : fromWeekDate 2023 3 2 == fromGregorian dt_2023_1_17 := by rfl

example : fromWeekDateValid 2023 3 2 == some (fromGregorian dt_2023_1_17) := by rfl

example : (NonemptyIcc.toFin <| clipToNonemptyIcc 1 12 3 (by simp_arith)) == Fin.ofNat' 12 2 := by rfl

def dt_2023_2_11 : Date := date% 2023-2-11

def dt_2023_2_12 : Date := date% 2023-2-12

example : (fromWeekDateValid 2023 6 7 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : (fromMondayStartWeekValid 2023 6 7 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : (fromSundayStartWeekValid 2023 7 0 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : Gregorian.addDays 1 dt_2023_2_11 == dt_2023_2_12 := by rfl

example : Gregorian.addMonthsClip 1 (fromGregorianClipped 2005 1 30) == fromGregorianClipped 2005 2 28 := by rfl

example : Gregorian.addMonthsRollOver 1 (fromGregorianClipped 2005 1 30) == fromGregorianClipped 2005 3 2 := by rfl

example : (toOrdinalDate <| fromGregorianClipped 2004 2 29) ==
  ⟨2004, .leap ⟨60, And.intro (by simp_arith) (by simp_arith)⟩, (by simp_arith)⟩ := by rfl

example : (toOrdinalDate <| fromGregorianClipped 2004 12 31) ==
  ⟨2004, .leap ⟨366, And.intro (by simp_arith) (by simp)⟩, (by simp_arith)⟩ := by rfl

example : (toOrdinalDate <| fromGregorianClipped 2006 2 28) ==
  ⟨2006, .common ⟨59, And.intro (by simp_arith) (by simp_arith)⟩, (by simp_arith)⟩ := by rfl

example : (toOrdinalDate <| fromGregorianClipped 2006 12 31) ==
  ⟨2006, .common ⟨365, And.intro (by simp_arith) (by simp)⟩, (by simp_arith)⟩ := by rfl

example : Gregorian.addYearsClip 2 (fromGregorianClipped 2004 2 29) == fromGregorianClipped 2006 2 28 := by rfl

example : Gregorian.addYearsRollOver 2 (fromGregorianClipped 2004 2 29) == fromGregorianClipped 2006 3 1 := by rfl

example : Gregorian.diffDurationClip (fromGregorianClipped 2004 2 29) (fromGregorianClipped 2004 3 1)
              == ⟨ 0,-1⟩  := by rfl

example : Gregorian.addDays 1 (date% 2023-2-28) = (date% 2023-3-1) := by rfl
