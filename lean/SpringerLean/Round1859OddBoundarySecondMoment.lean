import SpringerLean.Round1858OddForwardCoefficient

namespace SpringerLean

theorem exteriorForwardCoeff_finite_two_thirds_margin_of_b2_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (h2 : exteriorForwardCoeff F 2 = 0) (N : ℕ) (hN : 3 ≤ N) :
    1 + (∑ j ∈ Finset.Icc 1 N, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      2 - (2 / 3 : ℝ) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let b : ℕ → ℝ := fun j => ‖exteriorForwardCoeff F j‖ ^ 2
  have hset : Finset.Icc 1 N = insert 1 (insert 2 (Finset.Icc 3 N)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot1 : 1 ∉ insert 2 (Finset.Icc 3 N) := by simp
  have hnot2 : 2 ∉ Finset.Icc 3 N := by simp
  have harea := exteriorForwardCoeff_finite_area F hc N
  rw [hset, Finset.sum_insert hnot1, Finset.sum_insert hnot2] at harea ⊢
  simp only [h2, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    Nat.cast_one, one_mul, add_zero] at harea ⊢
  have hweight : 3 * (∑ j ∈ Finset.Icc 3 N, b j) ≤
      ∑ j ∈ Finset.Icc 3 N, (j : ℝ) * b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact mul_le_mul_of_nonneg_right hj3 (sq_nonneg _)
  dsimp only [b] at hweight
  linarith

theorem exteriorForwardCoeff_tsum_two_thirds_margin_of_b2_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (h2 : exteriorForwardCoeff F 2 = 0) :
    1 + (∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      2 - (2 / 3 : ℝ) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  have hsum := (exteriorForwardCoeff_sq_summable F hc).hasSum
  apply le_of_tendsto (hsum.tendsto_sum_nat.const_add 1)
  filter_upwards [Filter.eventually_ge_atTop 4] with M hM
  have hset : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : 0 ∉ Finset.Icc 1 (M - 1) := by simp
  rw [hset, Finset.sum_insert hnot]
  simp only [exteriorForwardCoeff_zero, norm_zero,
    zero_pow (by norm_num : 2 ≠ 0), zero_add]
  exact exteriorForwardCoeff_finite_two_thirds_margin_of_b2_zero F hc h2
    (M - 1) (by omega)

/-- The actual odd-map moment deficit used after the power-map step in
the even-star argument.  It is independent of inverse-coefficient bounds
and of the full real-exponent radial-moment theorem. -/
theorem actualBoundaryRadialMoment_two_odd_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hodd : ∀ z ∈ exteriorDisk, F (-z) = -F z) :
    actualBoundaryRadialMoment F 2 ≤
      2 - (2 / 3 : ℝ) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  rw [actualBoundaryRadialMoment_two_eq_coeff F hc]
  exact exteriorForwardCoeff_tsum_two_thirds_margin_of_b2_zero F hc
    (exteriorForwardCoeff_two_eq_zero_of_odd F hodd)

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_two_odd_margin
