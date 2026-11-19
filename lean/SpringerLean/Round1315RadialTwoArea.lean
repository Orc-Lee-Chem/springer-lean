import SpringerLean.AreaFinite
import SpringerLean.GeneralArea

namespace SpringerLean

/-- The part of the exterior area budget beyond the first Laurent
coefficient is at most half of its unused budget.  This uses the actual
centered exterior class, not a certificate-success hypothesis. -/
theorem exteriorForwardCoeff_tail_sq_le_half_deficit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ j ∈ Finset.Icc 2 N, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 2 := by
  let b : ℕ → ℝ := fun j => ‖exteriorForwardCoeff F j‖ ^ 2
  have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Icc 2 N := by simp
  have harea := exteriorForwardCoeff_finite_area F hc N
  have hsplit :
      b 1 + (∑ j ∈ Finset.Icc 2 N, (j : ℝ) * b j) ≤ 1 := by
    rw [hset, Finset.sum_insert hnot] at harea
    simpa only [Nat.cast_one, one_mul, b] using harea
  have hweight :
      2 * (∑ j ∈ Finset.Icc 2 N, b j) ≤
        ∑ j ∈ Finset.Icc 2 N, (j : ℝ) * b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj2 : (2 : ℝ) ≤ j := by
      exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact mul_le_mul_of_nonneg_right hj2 (sq_nonneg _)
  dsimp only [b] at hsplit hweight ⊢
  linarith

/-- Finite-coefficient form of the sharp p=2 radial moment margin.
The separate boundary Parseval passage is still required to identify
its left side with the actual radial trace integral. -/
theorem exteriorForwardCoeff_finite_radial_two_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (hN : 2 ≤ N) :
    1 + (∑ j ∈ Finset.Icc 1 N, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      2 * (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) := by
  have htail := exteriorForwardCoeff_tail_sq_le_half_deficit F hc N hN
  have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : 1 ∉ Finset.Icc 2 N := by simp
  rw [hset, Finset.sum_insert hnot]
  linarith

/-- Equality in any finite p=2 Parseval truncation forces the actual
exterior map to be a unit slit.  Identification of this truncation with
the almost-everywhere boundary moment is a separate analytic theorem. -/
theorem exteriorForwardCoeff_finite_radial_two_eq_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (N : ℕ) (hN : 2 ≤ N)
    (hEq : 1 + (∑ j ∈ Finset.Icc 1 N,
      ‖exteriorForwardCoeff F j‖ ^ 2) = (2 : ℝ)) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  have hmargin := exteriorForwardCoeff_finite_radial_two_margin F hc N hN
  have hβle : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
      exteriorInverseCoeff_one_norm_le F hc
  have hβ : ‖exteriorForwardCoeff F 1‖ = 1 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp
  simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hβ

end SpringerLean
