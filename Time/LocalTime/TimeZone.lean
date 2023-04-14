namespace Time

structure TimeZone where
  timeZoneMinutes : Int
  timeZoneSummerOnly : Bool
  timeZoneName : String
  deriving Repr, BEq

instance : Inhabited TimeZone where
  default := ⟨0,false,""⟩

namespace TimeZone

@[extern "lean_get_current_timezone"]
opaque get_current_timezone : IO (Int × Int × String)

def getTimeZone : IO TimeZone := do
  let tuple ← get_current_timezone
  return {timeZoneMinutes := tuple.1 / 60, timeZoneSummerOnly := tuple.2.1 == 1, timeZoneName := tuple.2.2 }

instance : ToString TimeZone where
  toString a := s!"tz: ({a.timeZoneMinutes}, {a.timeZoneSummerOnly}, {a.timeZoneName})"

def minutesToTimeZone (m : Int) : TimeZone := ⟨m, false, ""⟩
