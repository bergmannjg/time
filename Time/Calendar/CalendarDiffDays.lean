namespace Time

structure CalendarDiffDays  where
  months : Int
  days : Int
  deriving Repr, BEq

instance : Inhabited CalendarDiffDays where
  default := ⟨0, 0⟩

def calendarDay : CalendarDiffDays := ⟨0, 1⟩

def calendarWeek : CalendarDiffDays := ⟨0, 7⟩

def calendarMonth : CalendarDiffDays := ⟨1, 0⟩

def calendarYear : CalendarDiffDays := ⟨12, 0⟩
