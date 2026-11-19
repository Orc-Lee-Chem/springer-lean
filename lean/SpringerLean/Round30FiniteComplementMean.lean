import SpringerLean.Round30ComparisonCircleIntegrable
import SpringerLean.Round30ComparisonOuterMean
import SpringerLean.Round27ActualIntegratedSubmean

open MeasureTheory Set Metric

namespace SpringerLean

/-- The bounded part of the actual finite complement is subharmonic in the
horizontal complex parameter. The comparison term is harmonic because its
vertical sources stay outside the circle of radius ρ<h. -/
theorem regularExterior_finite_complement_bounded_part_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a h T ρ : ℝ) (hh : 0 < h) (hT : h ≤ T)
    (hES : E ⊆ Icc (-T) T) (hρ : 0 < ρ) (hρh : ρ < h) :
    (∫ t in Icc (-T) T \ E,
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t in Icc (-T) T \ Icc (-h) h,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) ≤
    Real.circleAverage
      (fun z : ℂ =>
        (∫ t in Icc (-T) T \ E,
          regularExteriorRotatedPotential F s ξ
            (z + (t : ℂ) * Complex.I)) -
        (∫ t in Icc (-T) T \ Icc (-h) h,
          comparisonSegmentPotential (z + (t : ℂ) * Complex.I)))
      (a : ℂ) ρ := by
  let A : Set ℝ := Icc (-T) T \ E
  let B : Set ℝ := Icc (-T) T \ Icc (-h) h
  have hAm : MeasurableSet A := measurableSet_Icc.diff hEm
  have hBm : MeasurableSet B := measurableSet_Icc.diff measurableSet_Icc
  have hAb : Bornology.IsBounded A := (isBounded_Icc (-T) T).subset diff_subset
  have hBb : Bornology.IsBounded B := (isBounded_Icc (-T) T).subset diff_subset
  have hsep : ∀ t ∈ B, h ≤ |t| := by
    intro t ht
    have hnot : t ∉ Icc (-h) h := ht.2
    by_cases hneg : t < -h
    · rw [abs_of_neg (by linarith)]
      linarith
    · have hpos : h < t := by
        by_contra hn
        apply hnot
        exact ⟨by linarith, by linarith⟩
      rw [abs_of_pos (by linarith)]
      linarith
  have hg := regularExterior_rotated_potential_vertical_integral_submean
    F hc hs0 hs1 ξ hξ A hAm hAb (a : ℂ) ρ hρ
  have hG := comparisonSegmentPotential_vertical_integral_circleAverage_eq_of_sep
    B hBm hBb a h ρ hρ hρh hsep
  have hgci := regularExterior_rotated_potential_vertical_set_circleIntegrable
    F hc hs0 hs1 ξ hξ A hAm hAb (a : ℂ) ρ
  have hGci := comparisonSegmentPotential_vertical_set_circleIntegrable_of_sep
    B hBm hBb a h ρ hρ.le hρh hsep
  change (∫ t in A, regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t in B, comparisonSegmentPotential
      ((a : ℂ) + (t : ℂ) * Complex.I)) ≤
    Real.circleAverage
      (fun z : ℂ =>
        (∫ t in A, regularExteriorRotatedPotential F s ξ
          (z + (t : ℂ) * Complex.I)) -
        (∫ t in B, comparisonSegmentPotential
          (z + (t : ℂ) * Complex.I)))
      (a : ℂ) ρ
  rw [Real.circleAverage_fun_sub hgci hGci]
  linarith

end SpringerLean