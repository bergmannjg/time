import Test.Parse
import Test.Format
import Test.Fixed
import Test.Calendar

import Time

open Time

def main : IO Unit := do
  let tz <- TimeZone.getTimeZone
  IO.println s!"'timezone {tz}'"
  let time <- getSystemTime
  let time1 <- getSystemTime
  let diff := (UTCTime.toUTCTime time) - (UTCTime.toUTCTime time1)
  IO.println s!"time {time} {time1}, diffTime {diff}"
  let now <- ZonedTime.getZonedTime
  IO.println s!"time '{now}', asISO8601: '{toISO8601 now}'"
