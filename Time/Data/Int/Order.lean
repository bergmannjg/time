import Init.Data.Int.Order

theorem Int.lt_of_ediv_eq {a b : Int} {n : Nat} (hb : 0 < b) (h : a / b = n) : a < b + n * b := by
  rw [← Int.emod_add_ediv a b, h]
  have hx : a % b < b := by exact Int.emod_lt_of_pos _ hb
  simp [Int.sub_lt_sub_right _ _]
  rw [Int.mul_comm]
  simp [Int.add_lt_add_right hx _]
