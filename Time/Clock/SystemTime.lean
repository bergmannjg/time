import Time.ZeroPad

namespace Time

@[extern "lean_clock_gettime"]
opaque clock_gettime : IO (Int × UInt32)

/--  Get the system time, epoch start of 1970 UTC, leap-seconds ignored. -/
def getSystemTime : IO {t : IO.FS.SystemTime // t.nsec.toNat < 10 ^ 9} := do
  let tuple ← clock_gettime
  if h : tuple.2.toNat < 10 ^ 9
  then return ⟨{ sec := tuple.1 , nsec := tuple.2 }, h⟩
  else throw (IO.Error.userError "invalid nsec value")

instance : ToString IO.FS.SystemTime where
  toString a := s!"{a.sec}.{toZeroPadded a.nsec.toNat 9}"
