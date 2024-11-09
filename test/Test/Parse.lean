import Time

open Time
open Time.Notation

open Lean Parsec

-- Date

def parseDate? (fmt : String) (s : String) : Option Date := parse TimeLocale.deDETimeLocale fmt s

def dtDate : Date := date% 2023-2-12

example : (toGregorian <| fromGregorianDate dtDate) == dtDate := by rfl

example : parseDate? "%Y-%m-%d" "2023-02-12" == some dtDate := by native_decide

example : parseDate? "%Y-%b-%d" "2023-Feb-12" == some dtDate := by native_decide

example : parseDate? "%Y-%B-%d" "2023-Februar-12" == some dtDate := by native_decide

example : parseDate? "%Y-%j" "2023-043" == some dtDate := by native_decide

example : parseDate? "%Y-%V-%u" "2023-06-7" == some dtDate := by native_decide

example : parseDate? "%Y-%V-%a" "2023-06-So" == some dtDate := by native_decide

example : parseDate? "%Y-%V-%A" "2023-06-Sonntag" == some dtDate := by native_decide

-- TimeOfDay

def parseTimeOfDay? (fmt : String) (s : String) : Option TimeOfDay :=
  parse TimeLocale.defaultTimeLocale fmt s

def dtTimeOfDay1 : TimeOfDay := time% 12:24:30

def dtTimeOfDay2 : TimeOfDay := time% 12:24:30.1234

def dtTimeOfDay3 : TimeOfDay := time% 12:24:30.000000020

example : dtTimeOfDay2.Second.val.val = 30123400000 := by native_decide

example : dtTimeOfDay3.Second.val.val = 30000000020 := by native_decide

example : parseTimeOfDay? "%H:%M:%S" "12:24:30" == dtTimeOfDay1 := by native_decide

example : parseTimeOfDay? "%H:%M:%S%Q" "12:24:30.1234" == dtTimeOfDay2 := by native_decide

example : parseTimeOfDay? "%H:%M:%S%Q" "12:24:30" == dtTimeOfDay1 := by native_decide

example : parseTimeOfDay? "%H:%M:%S.%q" "12:24:30.000000020" == dtTimeOfDay3 := by native_decide

example : parseTimeOfDay? "%R:%S" "12:24:30" == dtTimeOfDay1 := by native_decide

example : parseTimeOfDay? "%T" "12:24:30" == dtTimeOfDay1 := by native_decide

-- LocalTime

def parseLocalTime? (fmt : String) (s : String) : Option LocalTime :=
  parse TimeLocale.defaultTimeLocale fmt s

def dtLocalTime : LocalTime := datetime% 2023-2-12 12:24:30

example : parseLocalTime? "%Y%m%d%H%M%S" "20230212122430" == dtLocalTime := by native_decide

example : parseLocalTime? "%Y-%m-%dT%H:%M:%S" "2023-02-12T12:24:30" == dtLocalTime := by
  native_decide

-- ZonedTime

def parseZonedTime? (fmt : String) (s : String) : Option ZonedTime :=
  parse TimeLocale.defaultTimeLocale fmt s

def dtZonedTime : Option ZonedTime := some ⟨datetime% 2023-2-12 12:24:30, ⟨60,false,""⟩⟩

example : parseZonedTime? "%Y-%m-%dT%H:%M:%S%Ez" "2023-02-12T12:24:30+01:00" == dtZonedTime := by
  native_decide

example :
  (match
    ("2022-11-20T10:40:00+01:00".toZonedTime? TimeLocale.defaultTimeLocale),
    ("2022-11-20T10:35:00+00:00".toZonedTime? TimeLocale.defaultTimeLocale) with
  | some dt1, some dt2 => dt1 - dt2
  | _, _ => Time.DiffTime.fromSec 0)
  == Time.DiffTime.fromSec (-3300) := by native_decide
