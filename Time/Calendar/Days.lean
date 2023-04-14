namespace Time

/--
Modified Julian Day is a standard count of days, with zero being the day 1858-11-17
-/
structure Day where
  modifiedJulianDay : Int
  deriving Repr, BEq

instance : ToString Day where
  toString a := s!"mjd : {a.modifiedJulianDay}"

/-- modified julian day of january 1, year 1 -/
instance : Inhabited Day where
  default := ⟨-678575⟩

namespace Day

def addDays (n : Int) (day : Day) : Day :=
  ⟨day.modifiedJulianDay + n⟩

def diffDays (day1 : Day) (day2 : Day) : Int :=
  day1.modifiedJulianDay - day2.modifiedJulianDay

protected def lt (a b : Day) : Prop := a.modifiedJulianDay < b.modifiedJulianDay
protected def le (a b : Day) : Prop := a.modifiedJulianDay ≤ b.modifiedJulianDay

instance : LT Day := ⟨Day.lt⟩
instance : LE Day := ⟨Day.le⟩

instance (a b : Day) : Decidable (a < b) := Int.decLt _ _
instance (a b : Day) : Decidable (a ≤ b) := Int.decLe _ _
