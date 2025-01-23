import Time.ZeroPad
import Time.Fixed

namespace Time

/-- digits of nano second -/
def Nano := 9

/-- This is a length of time in nsecs, as measured by a clock.  -/
structure DiffTime where
  val : Fixed Nano
  deriving Repr, BEq

namespace DiffTime

def fromSecNsec (sign : Sign) (sec : Nat) (nsec : Nat) (h : nsec < 10 ^ 9) : DiffTime :=
  ⟨Fixed.toFixed sign sec (Fixed.toDenominator nsec Nano h)⟩

def fromSec (sec : Int) : DiffTime := ⟨Fixed.toFixed (Fixed.toSign sec) (Int.natAbs sec) default⟩

def toSec (dt : DiffTime) : Int :=
  let p := Fixed.toParts dt.val
  match p.sign with | .Neg =>  -p.numerator | .Nonneg => p.numerator

instance : ToString DiffTime where toString a := s!"{a.val}"

def sub (dt1 dt2 : DiffTime) : DiffTime := ⟨dt1.val - dt2.val⟩

def add (dt1 dt2 : DiffTime) : DiffTime := ⟨dt1.val + dt2.val⟩

instance : Sub DiffTime where sub := sub

instance : Add DiffTime where add := add
