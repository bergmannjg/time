import Time.LocalTime.TimeZone

namespace Time

structure TimeLocale where
  /-- full and abbreviated week days, starting with Sunday -/
  wDays : List (String × String)
  /-- full and abbreviated months -/
  months : List (String × String)
  /-- AM\/PM symbols -/
  amPm : String × String
  /-- date and time format format string -/
  dateTimeFmt : String
  /-- date format format format string -/
  dateFmt : String
  /-- time format format format string-/
  timeFmt : String
  /-- time format when using 12h clock format -/
  time12Fmt : String
  /-- time zones known by name -/
  knownTimeZones : List TimeZone
  deriving Repr, BEq

private def encS (s : String) := "\"" ++ s ++ "\""

private def encL (l : List (String × String)) := l |> List.map (λ (s1, s2) => (encS s1, encS s2))

instance : ToString TimeLocale where
  toString a := s!"wDays:={encL a.wDays},months:={encL a.months},amPm:={a.amPm},dateTimeFmt:={encS a.dateTimeFmt},dateFmt:={encS a.dateFmt},timeFmt:={encS a.timeFmt},time12Fmt:={encS a.time12Fmt}"

namespace TimeLocale

def defaultTimeZones : List TimeZone :=
  [ TimeZone.mk 0 False "UT"
  , TimeZone.mk 0 False "GMT"
  , TimeZone.mk 0 False "WET"
  , TimeZone.mk (-5 * 60) False "EST"
  , TimeZone.mk (-4 * 60) True "EDT"
  , TimeZone.mk (-6 * 60) False "CST"
  , TimeZone.mk (-5 * 60) True "CDT"
  , TimeZone.mk (-7 * 60) False "MST"
  , TimeZone.mk (-6 * 60) True "MDT"
  , TimeZone.mk (-8 * 60) False "PST"
  , TimeZone.mk (-7 * 60) True "PDT"
  , TimeZone.mk (1 * 60) False "CET"
  , TimeZone.mk (1 * 60) True "CEST"
  , TimeZone.mk (2 * 60) False "EET"
  , TimeZone.mk (2 * 60) True "EEST"
  ]

/-- Locale representing American usage. -/
def enUSTimeLocale : TimeLocale :=
  { wDays :=
      [ ("Sunday", "Sun")
      , ("Monday", "Mon")
      , ("Tuesday", "Tue")
      , ("Wednesday", "Wed")
      , ("Thursday", "Thu")
      , ("Friday", "Fri")
      , ("Saturday", "Sat")
      ]
    months :=
      [ ("January", "Jan")
      , ("February", "Feb")
      , ("March", "Mar")
      , ("April", "Apr")
      , ("May", "May")
      , ("June", "Jun")
      , ("July", "Jul")
      , ("August", "Aug")
      , ("September", "Sep")
      , ("October", "Oct")
      , ("November", "Nov")
      , ("December", "Dec")
      ]
    amPm := ("AM", "PM")
    dateTimeFmt := "%a %b %e %H:%M:%S %Z %Y"
    dateFmt := "%m/%d/%y"
    timeFmt := "%H:%M:%S"
    time12Fmt := "%I:%M:%S %p"
    knownTimeZones := defaultTimeZones }

/-- Locale representing German usage. -/
def deDETimeLocale : TimeLocale :=
  { wDays := [("Sonntag", "So"), ("Montag", "Mo"), ("Dienstag", "Di"), ("Mittwoch", "Mi"), ("Donnerstag", "Do"), ("Freitag", "Fr"), ("Samstag", "Sa")]
    months := [("Januar", "Jan"), ("Februar", "Feb"), ("März", "Mär"), ("April", "Apr"), ("Mai", "Mai"), ("Juni", "Jun"), ("Juli", "Jul"), ("August", "Aug"), ("September", "Sep"), ("Oktober", "Okt"), ("November", "Nov"), ("Dezember", "Dez")]
    amPm := ("AM", "PM")
    dateTimeFmt := "%a %d %b %Y %T %Z"
    dateFmt := "%d.%m.%Y"
    timeFmt := "%T"
    time12Fmt := "%T"
    knownTimeZones := defaultTimeZones }

def defaultTimeLocale := deDETimeLocale

/-- get locale-specific information with [locale](https://man7.org/linux/man-pages/man1/locale.1.html) command -/
def getLocaleData := do
  let s ← IO.Process.run { cmd := "locale", args := #["abday", "day", "abmon", "mon", "d_t_fmt", "d_fmt", "t_fmt", "t_fmt_ampm"] }
  return s.split (λ c => c == '\n')

private def split (s : String) :=
  s.split (λ c => c == ';')

/-- get current locale with `getLocaleData` -/
def currentLocale : IO <| TimeLocale := do
  match ← getLocaleData with
  | [abday, day, abmon, mon, d_t_fmt, d_fmt, t_fmt, t_fmt_ampm, _] =>
    return { defaultTimeLocale with
          wDays := List.zip (split day) (split abday)
          months := List.zip (split mon) (split abmon)
          amPm := ("AM", "PM")
          dateTimeFmt := d_t_fmt
          dateFmt := d_fmt
          timeFmt := t_fmt
          time12Fmt := if t_fmt_ampm != "" then t_fmt_ampm else t_fmt }
  | _ => return defaultTimeLocale
