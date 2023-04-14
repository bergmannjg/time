import Time

open Time
open Lean Parsec

example : toISO8601 (default : ZonedTime) == "1858-11-17T00:00:00+00:00" := by
  native_decide

private def parsedString (s : String) :=
  Time.toISO8601 <| Option.getD (s.toZonedTime? TimeLocale.defaultTimeLocale) default

example : parsedString "2022-11-20T10:35:00+01:00" == "2022-11-20T10:35:00+01:00" := by
  native_decide
