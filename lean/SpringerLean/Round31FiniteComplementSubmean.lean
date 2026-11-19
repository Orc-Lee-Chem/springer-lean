import SpringerLean.Round31FiniteComplementBridge
import SpringerLean.Round30ComparisonCircleIntegrable
import SpringerLean.Round30ActualCircleIntegrable

open MeasureTheory Set Metric

namespace SpringerLean

/-- Circle integrability of the bounded part of a genuine optimizer complement. -/
theorem regularVerticalBoundedComplement_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E)
    (a h T ρ : ℝ) (hh : 0 < h) (hρ : 0 < ρ) (hρh : ρ < h) :
    CircleIntegrable (regularVerticalBoundedComplement F s ξ h T E) (a : ℂ) ρ := by
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
  have hgci := regularExterior_rotated_potential_vertical_set_circleIntegrable
    F hc hs0 hs1 ξ hξ A hAm hAb (a : ℂ) ρ
  have hGci := comparisonSegmentPotential_vertical_set_circleIntegrable_of_sep
    B hBm hBb a h ρ hρ.le hρh hsep
  exact hgci.sub hGci

/-- The actual finite complement is circle integrable at every sufficiently small radius. -/
theorem regularVerticalFiniteComplement_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E)
    (a h T ρ : ℝ) (hh : 0 < h) (hT : h ≤ T)
    (hρ : 0 < ρ) (hρh : ρ < h) :
    CircleIntegrable
      (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E)
      (a : ℂ) ρ := by
  have hB := regularVerticalBoundedComplement_circleIntegrable
    F hc hs0 hs1 ξ hξ E hEm a h T ρ hh hρ hρh
  have hO := regularVerticalOuterTail_circleIntegrable
    F hc hs0 hs1 ξ hξ a T ρ hρ (lt_of_lt_of_le hρh hT)
  have heq : (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E) =
      (fun z => regularVerticalBoundedComplement F s ξ h T E z +
        regularVerticalOuterTail F s ξ T z) := by
    funext z
    exact regularVerticalFiniteComplement_at_complex F s ξ h T E z
  rw [heq]
  exact hB.add hO

/-- Actual finite-window complement plus compensated outer tail is subharmonic
in the horizontal parameter, with all bounds inside the original class. -/
theorem regularVerticalFiniteComplement_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a h T ρ : ℝ) (hh : 0 < h) (hT : h ≤ T)
    (hES : E ⊆ Icc (-T) T) (hρ : 0 < ρ) (hρh : ρ < h) :
    regularVerticalFiniteComplement F s ξ a h T 0 E ≤
      Real.circleAverage
        (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E)
        (a : ℂ) ρ := by
  have hB := regularExterior_finite_complement_bounded_part_submean
    F hc hs0 hs1 ξ hξ E hEm hEb a h T ρ hh hT hES hρ hρh
  have hO := regularVerticalOuterTail_circle_submean
    F hc hs0 hs1 ξ hξ a T ρ hρ (lt_of_lt_of_le hρh hT)
  have hBci := regularVerticalBoundedComplement_circleIntegrable
    F hc hs0 hs1 ξ hξ E hEm a h T ρ hh hρ hρh
  have hOci := regularVerticalOuterTail_circleIntegrable
    F hc hs0 hs1 ξ hξ a T ρ hρ (lt_of_lt_of_le hρh hT)
  have hcenter : regularVerticalFiniteComplement F s ξ a h T 0 E =
      regularVerticalBoundedComplement F s ξ h T E (a : ℂ) +
        regularVerticalOuterTail F s ξ T (a : ℂ) := by
    simpa only [Complex.ofReal_re, Complex.ofReal_im] using
      regularVerticalFiniteComplement_at_complex F s ξ h T E (a : ℂ)
  rw [hcenter]
  rw [show (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E) =
    (fun z => regularVerticalBoundedComplement F s ξ h T E z +
      regularVerticalOuterTail F s ξ T z) from by
      funext z
      exact regularVerticalFiniteComplement_at_complex F s ξ h T E z]
  rw [Real.circleAverage_fun_add hBci hOci]
  have hB' : regularVerticalBoundedComplement F s ξ h T E (a : ℂ) ≤
      Real.circleAverage (regularVerticalBoundedComplement F s ξ h T E) (a : ℂ) ρ := by
    have hfun :
        (fun z : ℂ =>
          (∫ t in Icc (-T) T \ E,
            regularExteriorRotatedPotential F s ξ (z + (t : ℂ) * Complex.I)) -
          (∫ t in Icc (-T) T \ Icc (-h) h,
            comparisonSegmentPotential (z + (t : ℂ) * Complex.I))) =
        regularVerticalBoundedComplement F s ξ h T E := rfl
    rw [hfun] at hB
    exact hB
  exact add_le_add hB' hO

end SpringerLean