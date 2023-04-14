import Time

open Time
open Lean Parsec Private

/-- see https://heasarc.gsfc.nasa.gov/cgi-bin/Tools/xTime/xTime.pl-/

def dt_1858_11_17 : Date := { Year := 1858, Month := ⟨11, (by simp)⟩, Day := ⟨17, (by simp)⟩ }

def dt_1997_1_1 : Date := { Year := 1997, Month := ⟨1, (by simp)⟩, Day := ⟨1, (by simp)⟩ }

def dt_2023_2_3 : Date := { Year := 2023, Month := ⟨2, (by simp)⟩, Day := ⟨3, (by simp)⟩ }

example : fromGregorianDate default == (default : Day) := by rfl

example : fromGregorian 0 12 31 == Day.addDays (-1)  (default : Day) := by rfl

example : fromGregorianDate dt_1858_11_17 == ⟨0⟩ := by rfl

example : fromGregorianDate dt_1997_1_1 == ⟨50449⟩ := by rfl

example : fromGregorian 1997 1 1 == ⟨50449⟩ := by rfl

example : fromGregorianValid 1997 1 1 == some ⟨50449⟩ := by rfl

example : toGregorian ⟨50449⟩ == ⟨1997, ⟨1, (by simp)⟩, ⟨1, (by simp)⟩⟩ := by rfl

example : toGregorian (fromGregorianDate dt_2023_2_3) == ⟨2023, ⟨2, (by simp)⟩, ⟨3, (by simp)⟩⟩
  := by rfl

example : toOrdinalDate default == ⟨1, ⟨1, by simp⟩⟩ := by rfl

example : toOrdinalDate ⟨0⟩  == ⟨1858, ⟨321, by simp⟩⟩ := by rfl

example : (toOrdinalDate <| fromOrdinalDate ⟨2023, ⟨50, by simp⟩⟩) == ⟨2023, ⟨50, by simp⟩⟩ := by rfl

def dt_2023_1_17 : Date := { Year := 2023, Month := ⟨1, (by simp)⟩, Day := ⟨17, (by simp)⟩ }

example : fromWeekDate 2023 3 2 == fromGregorianDate dt_2023_1_17 := by rfl

example : fromWeekDateValid 2023 3 2 == some (fromGregorianDate dt_2023_1_17) := by rfl

example : (NonemptyIcc.toFin <| clip' 1 12 3 (by simp)) == (Fin.ofNat 2 : Fin 12) := by rfl

def dt_2023_2_12 : Date := { Year := 2023, Month := ⟨2, (by simp)⟩, Day := ⟨12, (by simp)⟩ }

example : (fromWeekDateValid 2023 6 7 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : (fromMondayStartWeekValid 2023 6 7 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : (fromSundayStartWeekValid 2023 7 0 |> Option.map (λ dt => toGregorian dt))
  == some dt_2023_2_12 := by rfl

example : Gregorian.addMonthsClip 1 (fromGregorian 2005 1 30) == fromGregorian 2005 2 28 := by rfl

example : Gregorian.addMonthsRollOver 1 (fromGregorian 2005 1 30) == fromGregorian 2005 3 2 := by rfl

example : Gregorian.addYearsClip 2 (fromGregorian 2004 2 29) == fromGregorian 2006 2 28 := by rfl

example : Gregorian.addYearsRollOver 2 (fromGregorian 2004 2 29) == fromGregorian 2006 3 1 := by rfl

example : Gregorian.diffDurationClip (fromGregorian 2004 2 29) (fromGregorian 2004 3 1)
              == ⟨ 0,-1⟩  := by rfl
