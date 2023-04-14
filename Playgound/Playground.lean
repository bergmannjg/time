import Mathlib.Tactic.Find
import Mathlib.Tactic.HelpCmd
import Mathlib.Tactic.NormNum
import Std

--import Time

--set_option trace.Meta.Tactic.simp true

--set_option trace.Tactic.norm_num true in
example : 1 <= 28 := by norm_num1

--#eval fromWeekDate 2023 3 2

--#find (_ -> ToString _)
--#find ((_ : Int) / ?n <= _ / ?n)
#find ((?a:Nat) ≤ ?b → ?b <  ?c → ?a < ?c)
--#find ((?a:Int) < ?b → ?b ≤ ?c → ?a < ?c)
--#find ((?n:Int) ≤ ?m → ?n +?c ≤ ?m + ?c)
--#find ((?n:Int) ≤ ?m → (Int.toNat ?n) ≤ _)
--#find ((?n:Int) < ?m → ?n ≤ ?m)

--#find ((?n:Int) < ?m → (?n + 1) ≤ ?m)

--#find ( ¬((?n:Int) = ?m) ↔ ?n ≠ ?m)

--#find ((?n:Int) ≠ _ ↔ _ ≠ _)

--#find (((?a:Int) + ?b) * ?c = _)

--#find ((?a) + 0 = ?a)

--#help tactic

--set_option pp.coercions false in
--set_option trace.Meta.synthInstance true in
--set_option pp.explicit true in
