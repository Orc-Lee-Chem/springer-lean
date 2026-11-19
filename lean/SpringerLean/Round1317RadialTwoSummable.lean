import SpringerLean.Round1315RadialTwoArea
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace SpringerLean

/-- The actual forward Laurent coefficients are square summable.  This
is the Hilbert-space input for a general boundary Parseval theorem. -/
theorem exteriorForwardCoeff_sq_summable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Summable (fun j : ℕ => ‖exteriorForwardCoeff F j‖ ^ 2) := by
  apply summable_of_sum_range_le (c := (1 : ℝ)) (fun j => sq_nonneg _)
  intro M
  by_cases hM : M = 0
  · simp [hM]
  have hset : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot : 0 ∉ Finset.Icc 1 (M - 1) := by simp
  rw [hset, Finset.sum_insert hnot]
  simp only [exteriorForwardCoeff_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
  calc
    (∑ j ∈ Finset.Icc 1 (M - 1), ‖exteriorForwardCoeff F j‖ ^ 2)
        ≤ ∑ j ∈ Finset.Icc 1 (M - 1),
            (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hj1 : (1 : ℝ) ≤ j := by
            exact_mod_cast (Finset.mem_Icc.mp hj).1
          nlinarith [sq_nonneg (‖exteriorForwardCoeff F j‖)]
    _ ≤ 1 := exteriorForwardCoeff_finite_area F hc (M - 1)

/-- The coefficient-square series has the same quantitative p=2
margin as every finite truncation.  The a.e. radial boundary integral
is not identified with this tsum by this theorem. -/
theorem exteriorForwardCoeff_tsum_radial_two_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    1 + (∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
      2 * (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) := by
  have hsum := (exteriorForwardCoeff_sq_summable F hc).hasSum
  have hfinite (M : ℕ) (hM : 3 ≤ M) :
      1 + (∑ j ∈ Finset.range M, ‖exteriorForwardCoeff F j‖ ^ 2) ≤
        2 * (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) := by
    have hset : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hnot : 0 ∉ Finset.Icc 1 (M - 1) := by simp
    rw [hset, Finset.sum_insert hnot]
    simp only [exteriorForwardCoeff_zero, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact exteriorForwardCoeff_finite_radial_two_margin F hc (M - 1) (by omega)
  apply le_of_tendsto (hsum.tendsto_sum_nat.const_add 1)
  filter_upwards [Filter.eventually_ge_atTop 3] with M hM
  exact hfinite M hM

/-- Equality in the complete coefficient-square p=2 expression forces
the unit slit on the open exterior disk. -/
theorem exteriorForwardCoeff_tsum_radial_two_eq_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hEq : 1 + (∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2) = (2 : ℝ)) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  have hmargin := exteriorForwardCoeff_tsum_radial_two_margin F hc
  have hβle : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
      exteriorInverseCoeff_one_norm_le F hc
  have hβ : ‖exteriorForwardCoeff F 1‖ = 1 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp
  simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hβ

end SpringerLean
