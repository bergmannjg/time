import Mathlib.Tactic.NormNum
import Time.LocalTime.TimeZone
import Time.Clock.DiffTime
import Time.Calendar.Private
import Std

namespace Time

namespace Second

def zero : Fixed 9 := Fixed.zero

def sixty : Fixed 9 := Fixed.toFixed 60 0

end Second

abbrev Ico.Second := Set.Ico Second.zero Second.sixty

structure TimeOfDay where
  Hour : Set.Ico 0 24
  Minute : Set.Ico 0 60
  Second : Ico.Second
  deriving Repr, BEq

instance : ToString TimeOfDay where
  toString a := s!"tod : ({a.Hour}, {a.Minute}, {a.Second})"

instance : Inhabited TimeOfDay where
  default := ⟨⟨0, (by simp)⟩ , ⟨0, (by simp)⟩, ⟨Fixed.zero, (by simp_arith)⟩⟩

namespace TimeOfDay

def divMod (n : Int) (d : Nat) : Int × Int :=
  (n / d, n % d)

private def toIco (v : Int) (a b : Nat) (h1 : a ≤ v) (h2 : v < b) (hb : 0 < b) : Set.Ico a b :=
  let v' := v.toNat
  have h1' : a ≤ v' := Int.toNat_le_toNat h1
  have h2' : v' < b := (Int.toNat_lt_toNat (Int.ofNat_lt.mpr hb)).mpr h2

  ⟨v', And.intro h1' h2'⟩

private def divMod' (n : Int) (d : Nat) (hd : 0 < d) : Int ×  Set.Ico 0 d :=
  let mod := n % d
  have h1 : 0 ≤ mod := Int.emod_nonneg n (Int.coe_nat_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd))
  have h2 : mod < d := Int.emod_lt_of_pos n (Int.coe_nat_pos.mpr hd)

  (n / d, toIco mod 0 d h1 h2 hd)

def timeOfDayToTime (tod : TimeOfDay) : DiffTime :=
  let (_, _, d) := tod.Second.val.numeratorDenominator
  DiffTime.fromSecNsec ((tod.Hour * 60 + tod.Minute) * 60 + tod.Second.val.numerator) d

def timeToDaysAndTimeOfDay (secsOfTime : DiffTime) : Int × TimeOfDay :=
  let (m, ms) := Fixed.divMod' secsOfTime.val Second.sixty (by simp_arith)
  let (h, hm) := divMod' m 60 (by simp)
  let (days , dh) := divMod' h 24 (by simp)
  (days, ⟨ dh, hm, ms⟩)

def timeToTimeOfDay  (secsOfTime : DiffTime) : TimeOfDay :=
  (timeToDaysAndTimeOfDay secsOfTime).2

-- Convert a time of day in UTC to a time of day in some timezone, together with a day adjustment.
def utcToLocalTimeOfDay (zone : TimeZone) (tod : TimeOfDay) : Int × TimeOfDay :=
  let m' := tod.Minute + zone.timeZoneMinutes
  let (_, hm') := divMod' m' 60 (by simp)
  let h' := tod.Hour + (m' / 60)
  let (days , dh') := divMod' h' 24 (by simp)
  ( days, ⟨ dh', hm', tod.Second⟩ )

-- Convert a time of day  in some timezone to a time of day in UTC, together with a day adjustment.
def localToUTCTimeOfDay (zone : TimeZone) (tod : TimeOfDay) : Int × TimeOfDay :=
  utcToLocalTimeOfDay (TimeZone.minutesToTimeZone (Neg.neg (zone.timeZoneMinutes))) tod

def toSecond (secs : Int) (nanoSecs : Nat) (h1: 0 ≤ secs) (h2: secs < 60) : Ico.Second :=
  if h : 0 = secs then ⟨Second.zero, (by simp_arith)⟩
  else
    have h1' : 0 < secs := Int.lt_iff_le_and_ne.mpr (And.intro h1 (by simpa))
    ⟨Fixed.toFixed secs nanoSecs,
      And.intro
        (Fixed.toFixed_le_toFixed_of_lt 9 0 0 secs nanoSecs (by simp) h1')
        (Fixed.toFixed_lt_toFixed 9 secs nanoSecs 60 0 h1 h2)
    ⟩

def toSecond' (s : Private.NonemptyIco 0 60) : Ico.Second :=
  toSecond s.ico.val 0
    (Int.ofNat_le_ofNat_of_le s.ico.property.left)
    (Int.ofNat_lt_ofNat_of_lt s.ico.property.right)
