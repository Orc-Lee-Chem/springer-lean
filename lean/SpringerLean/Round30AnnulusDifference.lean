import SpringerLean.Round30ComparisonOutsideIntegrable

open MeasureTheory Set Metric

namespace SpringerLean

/-- On a bounded vertical set away from the comparison segment, the integral
of the compensated actual difference equals the difference of the two
individually integrable potentials. -/
theorem regularExterior_vertical_difference_setIntegral_eq_sub_of_sep
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (z : ℂ) (h ρ : ℝ) (hρ : 0 ≤ ρ) (hρh : ρ < h)
    (hz : |z.im| ≤ ρ) (hsep : ∀ t ∈ E, h ≤ |t|) :
    (∫ t in E,
      regularExteriorVerticalPotentialDifference F s ξ z.re (t + z.im)) =
    (∫ t in E, regularExteriorRotatedPotential F s ξ
      (z + (t : ℂ) * Complex.I)) -
    (∫ t in E, comparisonSegmentPotential
      (z + (t : ℂ) * Complex.I)) := by
  have hg : IntegrableOn
      (fun t : ℝ => regularExteriorRotatedPotential F s ξ
        (z + (t : ℂ) * Complex.I)) E := by
    have hc' : Continuous (fun t : ℝ =>
        regularExteriorRotatedPotential F s ξ
          (z + (t : ℂ) * Complex.I)) :=
      (regularExterior_rotated_potential_continuous
        F hc hs0 hs1 ξ hξ).comp (by fun_prop)
    exact (hc'.continuousOn.integrableOn_compact hEb.isCompact_closure).mono_set
      subset_closure
  have hG := comparisonSegmentPotential_vertical_set_integrableOn_of_sep
    E hEm hEb z h ρ hρ hρh hz hsep
  rw [← integral_sub hg hG]
  apply setIntegral_congr_fun hEm
  intro t ht
  exact regularExteriorVerticalPotentialDifference_at_complex F s ξ z t

end SpringerLean