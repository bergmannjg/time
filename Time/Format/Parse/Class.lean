import Lean.Data.Parsec
import Time.Format.Locale
import Time.Specifier

namespace Time

open Lean Parsec

class ReadMaybe (α : Type u) [Repr α] [BEq α] where
  readMaybe : String -> Option α

export ReadMaybe (readMaybe)

class MonadFail (m : Type u -> Type v) (α : Type u) where
  fail : String -> m α

export MonadFail (fail)

inductive ParseNumericPadding where
  | NoPadding
  | SpacePadding
  | ZeroPadding

class ParseTime (α : Type u) where
  substituteTimeSpecifier : TimeLocale -> SubstituteSpecifier -> String
  parseTimeSpecifier : TimeLocale -> Option ParseNumericPadding -> Specifier -> Parsec String
  buildTime : TimeLocale -> List (Specifier × String) -> Option α

mutual
  private partial def parse (α : Type u) [ParseTime α] : (l : TimeLocale) -> (fmts : List Char) -> Parsec <| List (Specifier × String)
    | l, '%' :: fmts => parse1 α l fmts
    | l, c :: fmts => do
      let _ ← pchar c
      parse α l fmts
    | _, _ => return []

  private partial def parse1 (α : Type u) [ParseTime α] : (l : TimeLocale) -> (fmts : List Char) -> Parsec <| List (Specifier × String)
    | l, '-' :: fmts => parse2 α l (some ParseNumericPadding.NoPadding) fmts
    | l, '_' :: fmts => parse2 α l (some ParseNumericPadding.SpacePadding) fmts
    | l, '0' :: fmts => parse2 α l (some ParseNumericPadding.ZeroPadding) fmts
    | l, fmts => parse2 α l none fmts

  private partial def parse2 (α : Type u) [ParseTime α] : (l : TimeLocale) ->  (mpad : Option ParseNumericPadding) -> (fmts : List Char) -> Parsec <| List (Specifier × String)
    | l, mpad, 'E' :: fmts => parse3 α l mpad fmts
    | l, mpad, fmts => parse3 α l mpad fmts

  private partial def parse3 (α : Type u) [ParseTime α] : (l : TimeLocale) -> (mpad : Option ParseNumericPadding) -> (fmts : List Char) -> Parsec <| List (Specifier × String)
    | l, _, '%' :: fmts => parse α l fmts
    | l, mpad, fmt :: fmts => do
        match toSubstituteSpecifier fmt with
        | some sp =>
          let s := ParseTime.substituteTimeSpecifier α l sp
          parse α l (s.toList ++ fmts)
        | none =>
          match toSpecifier fmt with
          | some s =>
            let res ←  ParseTime.parseTimeSpecifier α l mpad s
            let specs ← parse α l fmts
            return (s,res) :: specs
          | none => Parsec.fail s!"timeParseTimeSpecifier '{fmt}' failed"
    | _, _, [] => return []
end

def parseSpecifiers (α : Type u) [ParseTime α] (l : TimeLocale) (fmt : String) : Parsec <| List (Specifier × String) :=
  parse α l fmt.toList

def parseTime {α : Type} [ParseTime α] (l : TimeLocale) (fmt : String) : Parsec α := do
  let pairs ← parseSpecifiers α l fmt
  match ParseTime.buildTime l pairs with
  | some t => return t
  | none => Parsec.fail ""
