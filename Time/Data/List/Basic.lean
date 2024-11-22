
namespace List

/-- `findExisting p l h` returns the first element for which `p` returns true,
    and attaches membership and predicate `p` to element -/
def findExisting {α : Type } (p : α → Bool)
  (l : List α) (h : ∃ x ∈ l, p x) : { x // x ∈ l ∧ (p x) } :=
  have : l.length > 0 := by
    have : ∃ x, x ∈ l := by let ⟨a, h'⟩ := h; exact ⟨a, h'.left⟩
    exact List.length_pos_iff_exists_mem.mpr this
  match l with
  | a::as =>
    have hmem : a ∈ a :: as := by simp [List.mem_cons_self]
    match hm : p a with
    | true  => ⟨a, And.intro hmem hm⟩
    | false =>
        let ⟨x, _⟩  := findExisting p as (by simp_all)
        ⟨x, by simp_all⟩
