import Time.Calendar.Days

namespace Time

inductive DayOfWeek
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday
  deriving Repr, BEq

namespace DayOfWeek

def fromDayOfWeek : DayOfWeek -> Int
  | .Monday    => 1
  | .Tuesday   => 2
  | .Wednesday => 3
  | .Thursday  => 4
  | .Friday    => 5
  | .Saturday  => 6
  | .Sunday    => 7

def toDayOfWeek (n : Nat) : DayOfWeek :=
  match n  % 7 with
  | 0 => .Sunday
  | 1 => .Monday
  | 2 => .Tuesday
  | 3 => .Wednesday
  | 4 => .Thursday
  | 5 => .Friday
  | _ => .Saturday

def dayOfWeek (d : Day) : DayOfWeek :=
  toDayOfWeek <| (d.modifiedJulianDay.toNat + 3)
