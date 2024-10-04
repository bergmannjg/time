import Std.Internal.Parsec
import Time.Format.Parse.Class
import Time.Format.Parse.Instances
import Time.LocalTime.TimeOfDay
import Time.LocalTime.ZonedTime

namespace Time

open Lean Std.Internal Parsec.String

/-- Parses a time value (i.e. instance of ParseTime) given a format string (`Time.Specifier`) -/
def parse {α : Type} {m : Type -> Type v} [Monad m] [MonadFail m α] [ParseTime α] (l :
    TimeLocale) (fmt : String) (s : String) : m α := do
  match (parseTime l fmt : Parser α) s.mkIterator with
  | Parsec.ParseResult.success it res =>
    if it.hasNext then fail s!"remainingBytes {it.remainingBytes}" else return res
  | Parsec.ParseResult.error _ err => fail err

end Time

namespace String

open Time

/-- parse ZonedTime value from ISO 8601 string, e.g. '2023-02-02T19:55:03+01:00' -/
def toZonedTime? (l : TimeLocale) (s : String) : Option ZonedTime :=
  parse l "%Y-%m-%dT%H:%M:%S%Q%Ez" s

end String
