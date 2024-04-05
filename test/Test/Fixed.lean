import Time

open Lean Parsec

open Time
open Fixed

example : TimeOfDay.divMod 9 6 == (1, 3) := by rfl

example : divMod (.toFixed 9 0 : Fixed 3) (.toFixed 6 0) == (1, ⟨3000⟩) := by rfl

example : (divMod' (.toFixed 90 0 : Fixed 3) (.toFixed 60 0) (zero_lt_toFixed _ _ _ (by omega))
            : Int × (Time.Ico zero (toFixed 60 0)))
          == (1, ⟨(toFixed 30 0), And.intro
                (zero_le_toFixed _ _ _ (by omega))
                (toFixed_lt_toFixed _ _ _ _ _ (by omega) (by omega))
              ⟩) := by rfl

example : (toFixed 10 500 : Fixed 3) == ⟨10500⟩ := by rfl

example : (toFixed (-10) 500 : Fixed 3) == ⟨-10500⟩ := by rfl

example : (Fixed.zero : Fixed 3) - (toFixed 10 500 : Fixed 3) == ⟨-10500⟩ := by rfl

example : neg (toFixed 10 500 : Fixed 3) == ⟨-10500⟩ := by rfl

example : (toFixed 0 500 : Fixed 3) == ⟨500⟩ := by rfl

example : neg (toFixed 0 500 : Fixed 3) == ⟨-500⟩ := by rfl

example : numerator (toFixed 10 500 : Fixed 3) == 10 := by rfl

example : numeratorDenominator (toFixed 10 500 : Fixed 3) == (.Nonneg, 10, 500) := by rfl

example : numeratorDenominator (toFixed 10 500 : Fixed 3) == (.Nonneg, 10, 500) := by rfl

example : numeratorDenominator (neg (toFixed 0 500 : Fixed 3)) == (.Neg, 0, 500) := by rfl

example : (toFixed 1 500 : Fixed 3) - (toFixed 1 0 : Fixed 3) == ⟨500⟩ := by rfl

example : (toFixed 1 500 : Fixed 3) + (toFixed (-1) 0 : Fixed 3) == ⟨500⟩ := by rfl

example : (toFixed 1 0 : Fixed 3) - (toFixed 1 500 : Fixed 3) == ⟨-500⟩ := by rfl

example : (toFixed 1 0 : Fixed 3) - (toFixed 4 0 : Fixed 3) == ⟨-3000⟩ := by rfl

example : toString (toFixed 1 12300 : Fixed 5) == "1.123" := by native_decide

example : toString (toFixed 1 0 : Fixed 5) == "1" := by native_decide
