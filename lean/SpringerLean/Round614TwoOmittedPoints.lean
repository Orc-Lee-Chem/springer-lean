import SpringerLean.Round613ReciprocalAreaLower

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The sharp two-point omitted-set inequality for two actual omitted values.
The convex-hull extension is a separate convexity step. -/
theorem exteriorOmitted_two_point
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ exteriorOmitted F) (hP : P ∈ exteriorOmitted F) :
    4 * ‖A - P‖ + ‖A + P‖ ^ 2 ≤ 16 := by
  by_cases hAP : A = P
  · subst A
    have hp := exteriorOmitted_norm_le_two F hc hP
    have hn : ‖P + P‖ = 2 * ‖P‖ := by
      rw [← two_smul ℝ P, norm_smul]
      norm_num
    rw [sub_self, norm_zero, mul_zero, zero_add, hn]
    nlinarith [norm_nonneg P]
  obtain ⟨V,hV,hnz,hbV,hdV,hi,ha,hbudget,hupper⟩ :=
    exteriorOmitted_exists_midpoint_with_positive_area_budget F hc A P hA hP hAP
  have hl := exteriorReciprocal_deriv_energy_ge_inv_omitted_area V hV hnz hi ha
  have hscaled := mul_le_mul_of_nonneg_left hl (sq_nonneg (‖P - A‖ / 4))
  have hdiv : (‖P - A‖ / 4) ^ 2 / actualOmittedMoment V 0 ≤ actualOmittedMoment V 0 := by
    simpa only [div_eq_mul_inv,one_mul] using hscaled.trans hbudget
  have hs : (‖P - A‖ / 4) ^ 2 ≤ actualOmittedMoment V 0 ^ 2 := by
    simpa only [pow_two] using (div_le_iff₀ ha).mp hdiv
  have hqle : ‖P - A‖ / 4 ≤ actualOmittedMoment V 0 :=
    (sq_le_sq₀ (by positivity) ha.le).mp hs
  rw [norm_sub_rev] at hqle
  nlinarith

end SpringerLean
