import SpringerLean.LowOrder

namespace SpringerLean

/-- A reusable consequence of the finite exterior area estimate.
The area estimate is an explicit hypothesis here, never a field of the paper's
function class or an assumption of the all-order inverse formula. -/
theorem exteriorForwardCoeff_one_norm_le_of_finite_area
    (F : ℂ → ℂ)
    (harea : ∀ N : ℕ,
      (∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤ 1) :
    ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
  have h := harea 1
  simp at h
  nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]

/-- Equality in a finite area estimate forces every higher coefficient to vanish. -/
theorem exteriorForwardCoeff_eq_zero_of_finite_area_equality
    (F : ℂ → ℂ)
    (harea : ∀ N : ℕ,
      (∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤ 1)
    (hfirst : ‖exteriorForwardCoeff F 1‖ = 1)
    (j : ℕ) (hj : 2 ≤ j) :
    exteriorForwardCoeff F j = 0 := by
  let w : ℕ → ℝ := fun i => (i : ℝ) * ‖exteriorForwardCoeff F i‖ ^ 2
  have hsub : ({1, j} : Finset ℕ) ⊆ Finset.Icc 1 j := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hnonneg (i : ℕ) : 0 ≤ w i := by
    dsimp [w]
    positivity
  have hle : (∑ i ∈ ({1, j} : Finset ℕ), w i) ≤
      ∑ i ∈ Finset.Icc 1 j, w i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => hnonneg i)
  have hsum := le_trans hle (harea j)
  have hne : j ≠ 1 := by omega
  have hterm : w j ≤ 0 := by
    have hsum' : w 1 + w j ≤ 1 := by
      simpa [hne.symm] using hsum
    have hw1 : w 1 = 1 := by simp [w, hfirst]
    rw [hw1] at hsum'
    linarith
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hnormzero : ‖exteriorForwardCoeff F j‖ = 0 := by
    by_contra h
    have hn : 0 < ‖exteriorForwardCoeff F j‖ := lt_of_le_of_ne
      (norm_nonneg _) (Ne.symm h)
    have hw : 0 < w j := by
      dsimp [w]
      positivity
    exact (not_le_of_gt hw) hterm
  exact norm_eq_zero.mp hnormzero

end SpringerLean
