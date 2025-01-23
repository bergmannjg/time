import Time

open Lean Parsec

open Time
open Fixed

def ninety := (.toFixed Sign.Nonneg 90 default : Fixed 3)
def sixty := (.toFixed Sign.Nonneg 60 default : Fixed 3)
def thirty := (.toFixed Sign.Nonneg 30 default : Fixed 3)

example : ninety % sixty = thirty := by rfl

example : ninety / sixty = (1 : Int) := by rfl

example : ninety % sixty + (ninety / sixty) * sixty = ninety  := by rfl

example : Fixed.toMod ninety sixty (zero_lt_toFixed _ _ _ (by omega))
          == ⟨thirty, And.intro
                  (zero_le_toFixed _ _ _ (by omega))
                  (toFixed_lt_toFixed _ _ _ _ _ (by omega))
              ⟩ := by rfl

example : (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨10500⟩ := by native_decide

example : (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3)
          == (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3).toParts.fromParts := by native_decide

example : (⟨-50⟩ : Fixed 3) == (⟨-50⟩ : Fixed 3).toParts.fromParts := by rfl

example : (toFixed Sign.Neg 10 (toDenominator 500 3 (by simp)) : Fixed 3)
          == (toFixed Sign.Neg 10 (toDenominator 500 3 (by simp)) : Fixed 3).toParts.fromParts := by native_decide

example : (toFixed Sign.Neg 10 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨-10500⟩ := by native_decide

example : (Fixed.zero : Fixed 3) - (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3)
            == ⟨-10500⟩ := by native_decide

example : neg (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨-10500⟩ := by native_decide

example : (toFixed Sign.Nonneg 0 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨500⟩ := by native_decide

example : neg (toFixed Sign.Nonneg 0 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨-500⟩ := by native_decide

example : (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3).toParts.numerator == 10 := by native_decide

example : (toFixed Sign.Nonneg 10 (toDenominator 500 3 (by simp)) : Fixed 3).toParts
            == ⟨.Nonneg, 10, 500, by omega⟩ := by native_decide

example : (neg (toFixed Sign.Nonneg 0 (toDenominator 500 3 (by simp)) : Fixed 3)).toParts
            == ⟨.Neg, 0, 500, by omega⟩ := by native_decide

example : (toFixed Sign.Nonneg 1 (toDenominator 500 3 (by simp)) : Fixed 3)
            - (toFixed Sign.Nonneg 1 default : Fixed 3) == ⟨500⟩ := by native_decide

example : (toFixed Sign.Nonneg 1 (toDenominator 500 3 (by simp)) : Fixed 3)
            + (toFixed Sign.Neg 1 default : Fixed 3) == ⟨500⟩ := by native_decide

example : (toFixed Sign.Nonneg 1 default : Fixed 3)
            - (toFixed Sign.Nonneg 1 (toDenominator 500 3 (by simp)) : Fixed 3) == ⟨-500⟩ := by native_decide

example : (toFixed Sign.Nonneg 1 default : Fixed 3)
            - (toFixed Sign.Nonneg 4 default : Fixed 3) == ⟨-3000⟩ := by rfl

example : toString (toFixed Sign.Nonneg 1 (toDenominator 12300 5 (by simp)) : Fixed 5)
            == "1.123" := by native_decide

example : toString (toFixed Sign.Nonneg 1 default : Fixed 5) == "1" := by native_decide
