import Time.ZeroPad

namespace Time

@[extern "lean_clock_gettime"]
opaque clock_gettime : IO (Int × UInt32)

/--  Get the system time, epoch start of 1970 UTC, leap-seconds ignored. -/
def getSystemTime : IO IO.FS.SystemTime := do
  let tuple ← clock_gettime
  return { sec := tuple.1 , nsec := tuple.2 }

instance : ToString IO.FS.SystemTime where
  toString a := s!"{a.sec}.{toZeroPadded a.nsec.toNat 9}"
