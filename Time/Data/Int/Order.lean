import Init.Data.Int.Order
import Batteries.Data.Int.Order

theorem Int.toNat_lt_toNat {a b : Int} (h : a < b) (hb : 0 < b) : Int.toNat a < Int.toNat b := by
  unfold Int.toNat
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all

theorem Int.lt_toNat {n : Nat} {a : Int} (h : (n : Int) < a) (hb : 0 < a): n < Int.toNat a :=
  @Int.toNat_lt_toNat (Int.ofNat n) a h hb

theorem Int.toNat_le_toNat {a b : Int} (h : a ≤ b) : Int.toNat a ≤ Int.toNat b := by
  unfold Int.toNat
  split <;> try simp_all
  split <;> try simp_all
  rename_i n _ a
  have _ : (n : Int) < 0 := Int.lt_of_le_of_lt h (Int.negSucc_lt_zero a)
  contradiction

theorem Int.toNat_le {a : Int} {n : Nat} (h : a ≤ n) : Int.toNat a ≤ n :=
  @Int.toNat_le_toNat a (Int.ofNat n) h

theorem Int.le_of_eq {n m : Int} (h : n = m) : n ≤ m := by
  have : n + 0 = m := by simp_all [h]
  simp [Int.le.intro 0 this]

theorem Int.lt_of_ediv_eq {a b : Int} {n : Nat} (hb : 0 < b) (h : a / b = n) : a < b + n * b := by
  rw [← Int.emod_add_ediv a b, h]
  have hx : a % b < b := by exact Int.emod_lt_of_pos _ hb
  simp [Int.sub_lt_sub_right _ _]
  rw [Int.mul_comm]
  simp [Int.add_lt_add_right hx _]
