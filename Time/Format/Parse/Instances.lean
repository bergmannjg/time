import Std.Internal.Parsec
import Time.Format.Parse.Class
import Time.Calendar.WeekDate
import Time.LocalTime.TimeOfDay
import Time.LocalTime.LocalTime
import Time.LocalTime.ZonedTime
import Time.Specifier

namespace Parsec
open Lean Std.Internal Parsec Parsec.String

def count (n : Nat) (p : Parser α) : Parser <| List α :=
  List.replicate n p |>.mapM id

def choice : (List <| Parser α) -> Parser α
| [] => fail ""
| [p] => p
| p :: ps => attempt p <|> choice ps

def toNat (chars : List Char) :=
  chars.foldl (fun acc c => 10 * acc + (c.val.toNat - '0'.val.toNat)) 0

def nat (n : Nat) : Parser Nat := do
  return toNat (← count n digit)

def digits (n : Nat) : Parser String := do
  return List.asString (← count n digit)

def allowChar (c : Char) : Parser String :=
  (·.toString) <$> pchar c <|> return ""

end Parsec

namespace Time

open Lean Std.Internal Parsec Parsec.String

instance (α : Type) : MonadFail Option α where
  fail _ := none

instance (α : Type) : MonadFail Parser α where
  fail s := λ it => Parsec.ParseResult.error it s

instance : ReadMaybe String where
  readMaybe s := some s

instance : ReadMaybe Int where
  readMaybe s := s.toInt?

inductive PaddingSide where
  | PrePadding
  | PostPadding

inductive WeekType where
  | ISOWeek
  | SundayWeek
  | MondayWeek
  deriving Repr, BEq

inductive DayComponent where
  | DCCentury (y : Int) -- century of all years
  | DCCenturyYear (y : Int) -- 0-99, last two digits of both real years and week years
  | DCYearMonth (m : Int) -- 1-12
  | DCMonthDay (d : Int) -- 1-31
  | DCYearDay (dy : Int) -- 1-366
  | DCWeekDay (d : Int) -- 1-7 (mon-sun)
  | DCYearWeek (wt : WeekType) (wk : Int) -- 1-53 or 0-53
  deriving Repr, BEq

def DCCentury? : DayComponent -> Option Int | .DCCentury y => some y | _ => none
def DCCenturyYear? : DayComponent -> Option Int | .DCCenturyYear y => some y | _ => none
def DCYearMonth? : DayComponent -> Option Int | .DCYearMonth y => some y | _ => none
def DCMonthDay? : DayComponent -> Option Int | .DCMonthDay y => some y | _ => none
def DCYearDay? : DayComponent -> Option Int | .DCYearDay y => some y | _ => none
def DCWeekDay? : DayComponent -> Option Int | .DCWeekDay y => some y | _ => none
def DCYearWeek? : WeekType -> DayComponent -> Option Int
  | .ISOWeek, .DCYearWeek .ISOWeek y => some y
  | .SundayWeek, .DCYearWeek .SundayWeek y => some y
  | .MondayWeek, .DCYearWeek .MondayWeek y => some y
  | _, _ => none

def allowEmptyParser : Bool -> Parser String
| false => do
  let x ← many1 (digit)
  return x.toList.asString
| true => do
  let x ← many (digit)
  return x.toList.asString

def parsePaddedDigits : PaddingSide -> ParseNumericPadding -> Bool -> Nat -> Parser String
| _ , ParseNumericPadding.ZeroPadding, _, n => do
    let x ← count n (digit)
    return x.asString
| PaddingSide.PrePadding, ParseNumericPadding.SpacePadding, allowEmpty, _n =>
    ws *> allowEmptyParser allowEmpty
| PaddingSide.PostPadding, ParseNumericPadding.SpacePadding, allowEmpty, _n => do
    allowEmptyParser allowEmpty <* ws
| _ , ParseNumericPadding.NoPadding, false, _ => do
    let x ← many1 (digit)
    return x.toList.asString
| _ , ParseNumericPadding.NoPadding, true, _ => do
    let x ← many (digit)
    return x.toList.asString

def timeParseTimeSpecifier (l : TimeLocale) (mpad : Option ParseNumericPadding) (s : Specifier)
    : Parser String :=
  match s with
  -- century
  | .C => allowNegativeDigits ParseNumericPadding.SpacePadding 2
  | .f => allowNegativeDigits ParseNumericPadding.SpacePadding 2
  -- year
  | .Y => allowNegativeDigits ParseNumericPadding.ZeroPadding 4
  | .G => allowNegativeDigits ParseNumericPadding.SpacePadding 4
  -- year of century
  | .y => digits ParseNumericPadding.ZeroPadding 2
  | .g => digits ParseNumericPadding.ZeroPadding 2
  -- month of year
  | .B => oneOf (l.months.map (·.1))
  | .b => oneOf (l.months.map (·.2))
  | .m => digits ParseNumericPadding.ZeroPadding 2
  -- day of month
  | .d => digits ParseNumericPadding.ZeroPadding 2
  | .e => digits ParseNumericPadding.SpacePadding 2
  -- week of year
  | .V => digits ParseNumericPadding.ZeroPadding 2
  | .U => digits ParseNumericPadding.ZeroPadding 2
  | .W => digits ParseNumericPadding.ZeroPadding 2
  -- day of week
  | .u => oneOf ([1, 2, 3, 4 , 5, 6, 7].map toString)
  | .A => oneOf (l.wDays.map (·.1))
  | .a => oneOf (l.wDays.map (·.2))
  | .w => oneOf ([0, 1, 2, 3, 4 , 5, 6].map toString)
  -- day of year
  | .j => digits ParseNumericPadding.ZeroPadding 3
  -- hour of day (i.e. 24h)
  | .H => digits ParseNumericPadding.ZeroPadding 2
  -- minute of hour
  | .M => digits ParseNumericPadding.ZeroPadding 2
  -- second of minute
  | .S => digits ParseNumericPadding.ZeroPadding 2
  -- nanosecond of second
  | .q => digits' .PostPadding .ZeroPadding true Nano
  | .Q => attempt (pchar '.' *> digits' .PostPadding .NoPadding true Nano) <|> return ""
  -- time zone
  | .z => numericTZ
  | .Ez => numericTZ
  | .Z => numericTZ
  | .EZ => numericTZ
  | .l | .I | .k | .p | .P => Parsec.fail s!"specifier 'lIkpP' only valid in format"
  where
  digits' (ps : PaddingSide) (pad : ParseNumericPadding) (allowEmpty : Bool) (n : Nat)
      : Parser String :=
    parsePaddedDigits ps (Option.getD mpad pad) allowEmpty n
  digits (pad : ParseNumericPadding) (n : Nat) : Parser String :=
    digits' PaddingSide.PrePadding pad false n
  allowNegativeDigits (pad : ParseNumericPadding) (n : Nat) : Parser String := do
    let s1 := ← allowChar '-'
    let s2 ← digits' PaddingSide.PrePadding pad false n
    return s1 ++ s2
  oneOf (l : List String) : Parser String := choice <| l.map (pstring ·)
  numericTZ : Parser String := do
    let s ← pchar '+' <|> pchar '-'
    let h ← digits ParseNumericPadding.ZeroPadding 2
    let _ ← allowChar ':'
    let m ← digits ParseNumericPadding.ZeroPadding 2
    return s.toString ++ h ++ m

def timeSubstituteTimeSpecifier : TimeLocale -> SubstituteSpecifier -> String
  | l, .c => l.dateTimeFmt
  | _, .R => "%H:%M"
  | _, .T => "%H:%M:%S"
  | l, .X => l.timeFmt
  | l, .r => l.time12Fmt
  | _, .D => "%m/%d/%y"
  | _, .F => "%Y-%m-%d"
  | l, .x => l.dateFmt
  | _, .h => "%b"

def makeDayComponent (l : TimeLocale) (c : Specifier) (s : String) : Option <| List DayComponent
    := do
  match c with
  | .Y =>
    let a ← readMaybe s
    return [.DCCentury (a / 100), .DCCenturyYear (a % 100)]
  | .y =>
    let a ← readMaybe s
    return [.DCCentury a]
  | .B => do
    match indexOf? (·.1 == s) l.months with
    | some i => return [.DCYearMonth (i + 1)]
    | none => return []
  | .b =>
    match indexOf? (·.2 == s) l.months  with
    | some i => return [.DCYearMonth (i + 1)]
    | none => return []
  | .m =>
    let raw ← readMaybe s
    let a ← Clip.clip? 1 12 raw (by omega)
    return [.DCYearMonth a]
  | .d =>
    let raw ← readMaybe s
    let a ← Clip.clip? 1 31 raw (by omega)
    return [.DCMonthDay a]
  | .V =>
    let raw ← readMaybe s
    let a ← Clip.clip? 1 53 raw (by omega)
    return [.DCYearWeek WeekType.ISOWeek  a]
  | .U =>
    let raw ← readMaybe s
    let a ← Clip.clip? 0 53 raw (by omega)
    return [.DCYearWeek WeekType.SundayWeek  a]
  | .W =>
    let raw ← readMaybe s
    let a ← Clip.clip? 0 53 raw (by omega)
    return [.DCYearWeek WeekType.MondayWeek  a]
  | .u =>
    let raw ← readMaybe s
    let a ← Clip.clip? 1 7 raw (by omega)
    return [.DCWeekDay  a]
  | .a => do
    match indexOf? (·.2 == s) l.wDays with
    | some i' =>
      let i := if i' == 0 then 7 else i'
      return [.DCWeekDay i]
    | none => return []
  | .A => do
    match indexOf? (·.1 == s) l.wDays with
    | some i' =>
      let i := if i' == 0 then 7 else i'
      return [.DCWeekDay i]
    | none => return []
  | .w =>
    let raw ← readMaybe s
    let a ← Clip.clip? 0 6 raw (by omega)
    return [.DCWeekDay  a]
  | .j =>
    let raw ← readMaybe s
    let a ← Clip.clip? 1 366 raw (by omega)
    return [.DCYearDay a]
  | _ => return [] where
  indexOf? {α : Type} (p : α -> Bool) (l : List α) : Option Int :=
      if let some (i, _) := l.enum |>.find? (λ x => p x.2) then some i
      else none

def makeDayComponents (l : TimeLocale) (pairs : List (Specifier × String))
    : Option <| List DayComponent := do
  let components ← pairs.map (λ pair => makeDayComponent l pair.1 pair.2)
  return components |> List.filterMap id |> flatten where
  flatten {α : Type} (l : List <| List α) : List α := l.foldr (λ c acc => c ++ acc) []

def safeLast {α : Type} (a : α) (l : List α) : α :=
  List.getLast (a :: l) (by simp)

instance : ParseTime Day where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (l : TimeLocale) (pairs : List (Specifier × String)) := do
    let cs ← makeDayComponents l pairs
    rest cs cs where
    year (cs : List DayComponent) :=
      let d : Int := safeLast 70 (cs.filterMap DCCenturyYear?)
      let c : Int := safeLast (if d >= 69 then 19 else 20) (cs.filterMap DCCentury?)
      100 * c + d
    rest : List DayComponent -> List DayComponent -> Option Day
    | cs,  .DCYearMonth m :: _  =>
      let md := safeLast 1 (cs.filterMap DCMonthDay?)
      fromGregorianValid (year cs) m md
    | cs,  .DCYearDay yd :: _  =>
      fromOrdinalDateValid (year cs) yd
    | cs,  .DCYearWeek wt w ::_  =>
      let d : Int := safeLast 3 (cs.filterMap DCWeekDay?)
      let y := year cs
      match wt with
      | .ISOWeek => fromWeekDateValid y w d
      | .MondayWeek => fromMondayStartWeekValid y w d
      | .SundayWeek => fromSundayStartWeekValid y w d
    | cs, _ :: xs => rest cs xs
    | _, [] => none

instance : ParseTime Date where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (l : TimeLocale) (pairs : List (Specifier × String)) := do
    toGregorian (← ParseTime.buildTime l pairs)

instance : ParseTime TimeOfDay where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (_ : TimeLocale) (pairs : List (Specifier × String)) :=
    List.foldlM f default pairs where
    f (tod : TimeOfDay) (pair : Specifier × String) : Option TimeOfDay :=
      match pair.1 with
      | .H => do
        let raw ← readMaybe pair.2
        let a ← Clip.clipToNonemptyIco? 0 24 raw (by omega)
        some { tod with Hour := a }
      | .M => do
        let raw ← readMaybe pair.2
        let a ← Clip.clipToNonemptyIco? 0 60 raw (by omega)
        some { tod with Minute := a }
      | .S => do
        let raw ← readMaybe pair.2
        let a ← Clip.clipToNonemptyIco? 0 60 raw (by omega)
        some { tod with Second := TimeOfDay.toSecond' a }
      | .q => do
        let n : Int ← readMaybe pair.2
        let val := tod.Second.val + (Fixed.toFixed Sign.Nonneg 0 (Fixed.toDenominator n.toNat Nano) : Fixed Nano)
        let second ← Clip.clipToIco? Second.zero Second.sixty val
        some { tod with Second := second }
      | .Q => do
        let n : Int ← readMaybe (zeroRPad pair.2 Nano)
        let val := tod.Second.val + (Fixed.toFixed Sign.Nonneg 0 (Fixed.toDenominator n.toNat Nano) : Fixed Nano)
        let second ← Clip.clipToIco? Second.zero Second.sixty val
        some { tod with Second := second }
      | _ => some tod

instance : ParseTime LocalTime where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (l : TimeLocale) (pairs : List (Specifier × String)) :=
    LocalTime.mk <$> ParseTime.buildTime l pairs <*> ParseTime.buildTime l pairs

def readTzOffset (s : String) : Option Int :=
  match s.toList with
  | (s :: h1 :: h2 :: m1 :: m2 :: []) => calculate s h1 h2 m1 m2
  | _ => none
  where
  getSign : Char -> Option Int
    | '+' => some 1
    | '-' => some (-1)
    | _ => none
  calculate (s h1 h2 m1 m2 : Char) : Option Int := do
    let sign ←  getSign s
    let h ← readMaybe [h1, h2].asString
    let m ← readMaybe [m1, m2].asString
    return sign * (60 * h + m)

instance : ParseTime TimeZone where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (_ : TimeLocale) (pairs : List (Specifier × String)) :=
    List.foldlM f default pairs where
    f (tz : TimeZone) (pair : Specifier × String) : Option TimeZone :=
      match pair with
      | (.z, s) => do
        let offset ← readTzOffset s
        return ⟨offset, false, ""⟩
      | _ => some tz

instance : ParseTime ZonedTime where
  substituteTimeSpecifier := timeSubstituteTimeSpecifier
  parseTimeSpecifier := timeParseTimeSpecifier
  buildTime (l : TimeLocale) (pairs : List (Specifier × String)) :=
    ZonedTime.mk <$> ParseTime.buildTime l pairs <*> ParseTime.buildTime l pairs
