import SpringerLean.Round765PolynomialRolleLadder

namespace SpringerLean

/-- The number of points in a finite indexed list at or above a threshold. -/
noncomputable def upperGridCount (x : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℕ :=
  ∑ k ∈ Finset.range m, if t ≤ x k then 1 else 0

/-- Interlacing arrays have threshold counts differing by at most one.
This is the finite counting mechanism for the zero comparison in
Proposition 9.2. -/
theorem upperGridCount_interlacing (m : ℕ) (x y : ℕ → ℝ) (t : ℝ)
    (hxy : ∀ k < m, x (k + 1) ≤ y k ∧ y k ≤ x k) :
    upperGridCount y m t ≤ upperGridCount x (m + 1) t ∧
      upperGridCount x (m + 1) t ≤ upperGridCount y m t + 1 := by
  have hleft : (∑ k ∈ Finset.range m, if t ≤ y k then 1 else 0) ≤
      (∑ k ∈ Finset.range m, if t ≤ x k then 1 else 0) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := (hxy k (Finset.mem_range.mp hk)).2
    by_cases hy : t ≤ y k
    · have hx : t ≤ x k := hy.trans h
      simp [hy, hx]
    · simp [hy]
  have hright : (∑ k ∈ Finset.range m, if t ≤ x (k + 1) then 1 else 0) ≤
      (∑ k ∈ Finset.range m, if t ≤ y k then 1 else 0) := by
    apply Finset.sum_le_sum
    intro k hk
    have h := (hxy k (Finset.mem_range.mp hk)).1
    by_cases hx : t ≤ x (k + 1)
    · have hy : t ≤ y k := hx.trans h
      simp [hx, hy]
    · simp [hx]
  dsimp [upperGridCount]
  constructor
  · rw [Finset.sum_range_succ]
    omega
  · rw [Finset.sum_range_succ']
    have hzero : (if t ≤ x 0 then (1 : ℕ) else 0) ≤ 1 := by
      split_ifs <;> omega
    omega

/-- The first derivative Chebyshev zero grid and the original Chebyshev
zero grid differ by at most one point above any threshold. -/
theorem chebyshev_first_derivative_grid_count (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    upperGridCount
        (fun k : ℕ => Real.cos (((k : ℝ) + 1) * Real.pi / n)) (n - 1) t ≤
      upperGridCount
        (fun k : ℕ => Real.cos (((k : ℝ) + 1 / 2) * Real.pi / n)) n t ∧
    upperGridCount
        (fun k : ℕ => Real.cos (((k : ℝ) + 1 / 2) * Real.pi / n)) n t ≤
      upperGridCount
        (fun k : ℕ => Real.cos (((k : ℝ) + 1) * Real.pi / n)) (n - 1) t + 1 := by
  have hxy : ∀ k < n - 1,
      Real.cos ((((k + 1 : ℕ) : ℝ) + 1 / 2) * Real.pi / n) ≤
          Real.cos (((k : ℝ) + 1) * Real.pi / n) ∧
        Real.cos (((k : ℝ) + 1) * Real.pi / n) ≤
          Real.cos (((k : ℝ) + 1 / 2) * Real.pi / n) := by
    intro k hk
    have hk' : k + 1 < n := by omega
    obtain ⟨hleft, hright⟩ :=
      chebyshev_first_derivative_grid_interlaces n k hn hk'
    constructor
    · simpa only [ge_iff_le, Nat.cast_add, Nat.cast_one, add_assoc,
        show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] using hright
    · exact hleft
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
    upperGridCount_interlacing (n - 1)
      (fun k : ℕ => Real.cos (((k : ℝ) + 1 / 2) * Real.pi / n))
      (fun k : ℕ => Real.cos (((k : ℝ) + 1) * Real.pi / n)) t hxy

end SpringerLean

#print axioms SpringerLean.upperGridCount_interlacing
#print axioms SpringerLean.chebyshev_first_derivative_grid_count
