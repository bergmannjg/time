import Time.ZeroPad
import Time.Fixed

namespace Time

/-- This is a length of time in nsecs, as measured by a clock.  -/
structure DiffTime where
  val : Fixed 9
  deriving Repr, BEq

namespace DiffTime

def fromSecNsec (sec : Int) (nsec : Nat) : DiffTime := ⟨Fixed.toFixed sec nsec⟩

def fromSec (sec : Int) : DiffTime := ⟨Fixed.toFixed sec 0⟩

def toSec (dt : DiffTime) : Int := Fixed.numerator dt.val

instance : ToString DiffTime where toString a := s!"{a.val}"

def sub (dt1 dt2 : DiffTime) : DiffTime := ⟨dt1.val - dt2.val⟩

def add (dt1 dt2 : DiffTime) : DiffTime := ⟨dt1.val + dt2.val⟩

instance : Sub DiffTime where sub := sub

instance : Add DiffTime where add := add
