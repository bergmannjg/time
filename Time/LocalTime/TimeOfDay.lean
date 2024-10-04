import Init.Data.Int.DivMod
import Time.Data.Int.Order
import Time.LocalTime.TimeZone
import Time.Clock.DiffTime
import Time.Calendar.Clip
import Batteries

namespace Time

namespace Second

def zero : Fixed Nano := Fixed.zero

def sixty : Fixed Nano := Fixed.toFixed Sign.Nonneg 60 default

end Second

theorem zero_lt_sixty : Second.zero < Second.sixty := by
  unfold Second.zero Second.sixty
  simp_all [Fixed.zero_lt_toFixed _ _ _ _]

abbrev Ico.Second := Time.Ico Second.zero Second.sixty

structure TimeOfDay where
  Hour : Time.Ico 0 24
  Minute : Time.Ico 0 60
  Second : Ico.Second
  deriving Repr, BEq

instance : ToString TimeOfDay where
  toString a := s!"tod : ({a.Hour.val}, {a.Minute.val}, {a.Second.val})"

namespace TimeOfDay

private def toIco (v : Int) (a b : Nat) (h1 : a ≤ v) (h2 : v < b) (h3 : 0 < b) : Time.Ico a b :=
  let v' := v.toNat
  have h1' : a ≤ v' := Int.toNat_le_toNat h1
  have h2' : v' < b := Int.toNat_lt_toNat h2 (by omega)

  ⟨v', And.intro h1' h2'⟩

private def divMod (n : Int) (d : Nat) (hd : 0 < d) : Int ×  Time.Ico 0 d :=
  let mod := n % d
  have h1 : 0 ≤ mod := Int.emod_nonneg n (by omega)
  have h2 : mod < d := Int.emod_lt_of_pos n (by omega)

  (n / d, toIco mod 0 d h1 h2 hd)

def timeOfDayToTime (tod : TimeOfDay) : DiffTime :=
  let p := tod.Second.val.toParts
  DiffTime.fromSecNsec Sign.Nonneg ((tod.Hour.val * 60 + tod.Minute.val) * 60 + p.numerator) p.denominator

def timeToDaysAndTimeOfDay (secsOfTime : DiffTime) : Int × TimeOfDay :=
  let m := secsOfTime.val / Second.sixty
  let ms := Fixed.toMod secsOfTime.val Second.sixty
              (by unfold Second.sixty; simp_all [Fixed.zero_lt_toFixed _ _ _ _])
  let (h, hm) := divMod m 60 (by simp)
  let (days , dh) := divMod h 24 (by simp)
  (days, ⟨ dh, hm, ms⟩)

def timeToTimeOfDay  (secsOfTime : DiffTime) : TimeOfDay :=
  (timeToDaysAndTimeOfDay secsOfTime).2

-- Convert a time of day in UTC to a time of day in some timezone, together with a day adjustment.
def utcToLocalTimeOfDay (zone : TimeZone) (tod : TimeOfDay) : Int × TimeOfDay :=
  let m' := tod.Minute.val + zone.timeZoneMinutes
  let (_, hm') := divMod m' 60 (by simp)
  let h' := tod.Hour.val + (m' / 60)
  let (days , dh') := divMod h' 24 (by simp)
  ( days, ⟨ dh', hm', tod.Second⟩ )

-- Convert a time of day  in some timezone to a time of day in UTC, together with a day adjustment.
def localToUTCTimeOfDay (zone : TimeZone) (tod : TimeOfDay) : Int × TimeOfDay :=
  utcToLocalTimeOfDay (TimeZone.minutesToTimeZone (Neg.neg (zone.timeZoneMinutes))) tod

def toSecond (secs : Int) (nanoSecs : Nat) (h1: 0 ≤ secs) (h2: secs < 60) : Ico.Second :=
  if h : 0 = secs then ⟨Second.zero, And.intro (LeRefl.le_refl Fixed.zero) zero_lt_sixty⟩
  else
    let d_nanoSecs := Fixed.toDenominator nanoSecs Nano
    have h1 : 0 < secs := Int.lt_iff_le_and_ne.mpr (And.intro h1 (by simpa))
    have h1' : 0 < secs.toNat := Int.toNat_lt_toNat h1 h1
    have h2' : secs.toNat < 60 := Int.toNat_lt_toNat h2 (by omega)
    ⟨Fixed.toFixed Sign.Nonneg secs.toNat d_nanoSecs,
      And.intro
        (Fixed.toFixed_le_toFixed_of_lt Nano 0 default secs.toNat d_nanoSecs h1')
        (Fixed.toFixed_lt_toFixed Nano secs.toNat d_nanoSecs 60 default h2')
    ⟩

def toSecond' (s : NonemptyIco 0 60) : Ico.Second :=
  toSecond s.ico.val 0 (Int.ofNat_le.2 s.ico.property.left) (Int.ofNat_lt.2 s.ico.property.right)

namespace Time.Notation

/-- TimeOfDay syntactic category -/
declare_syntax_cat time
/-- TimeOfDay from numeric literals hour, minute, second and nanosecond -/
syntax num noWs ":" noWs num noWs ":" noWs scientific : time
/-- TimeOfDay from numeric literals hour, minute and second -/
syntax num noWs ":" noWs num (noWs ":" noWs num)? : time
syntax "time%" time : term

/--
  `time% hour:minute:second` is notation for
  `Time.TimeOfDay.mk ⟨hour, by omega⟩ ⟨minute, by omega⟩ (Time.TimeOfDay.toSecond second 0 (by omega) (by omega))`
  for the numeric literals hour, minute and second.
-/
macro_rules
| `(time% $h:num:$m:num:$s:scientific) =>
    let (mantissa, exponentSign, decimalExponent) := s.getScientific
    if !exponentSign
    then Lean.Macro.throwError "exponentSign expected"
    else
    if decimalExponent > Nano
    then Lean.Macro.throwError s!"expected decimalExponent ≤ {Nano}"
    else
      let sec := mantissa / (10^decimalExponent)
      let nsec := (mantissa % (10^decimalExponent)) * (10^(Nano-decimalExponent))
      `(Time.TimeOfDay.mk ⟨$h, by omega⟩ ⟨$m, by omega⟩
        (Time.TimeOfDay.toSecond $(Lean.Quote.quote sec) $(Lean.Quote.quote nsec) (by omega) (by omega)))
| `(time% $h:num:$m:num$[:$s:num]?) =>
    `(Time.TimeOfDay.mk ⟨$h, by omega⟩ ⟨$m, by omega⟩
      (Time.TimeOfDay.toSecond $(s.getD (Lean.Quote.quote 0)) 0 (by omega) (by omega)))

end Time.Notation

instance : Inhabited TimeOfDay where
  default := time% 0:0:0
