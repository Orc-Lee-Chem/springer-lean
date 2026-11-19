import SpringerLean.Round29AuxErrorBound

open MeasureTheory Set

namespace SpringerLean

/-- The actual auxiliary function is bounded by the two full-line L¹ errors
from the common radial reference, at every positive height. -/
theorem regularVerticalAuxiliary_le_reference_vertical_errors
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    regularVerticalAuxiliary F s ξ a h ≤
      ∫ t : ℝ,
        |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| +
        |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| := by
  obtain ⟨E, hE, hU⟩ :=
    regularVerticalAuxiliary_eq_of_actual_minimizer F hc hs0 hs1 ξ hξ a h hh
  let I : Set ℝ := Icc (-h) h
  let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let G : ℝ → ℝ := fun t => comparisonSegmentPotential
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let k : ℝ → ℝ := verticalReferenceKernel a
  have hI : MeasurableSet I := measurableSet_Icc
  have hkI : IntegrableOn k I := (verticalReferenceKernel_continuous a).integrableOn_Icc
  obtain ⟨T, hT⟩ := isBounded_iff_forall_norm_le.mp hE.2.1
  have hET : E ⊆ Icc (-T) T := by
    intro t ht
    have htT : |t| ≤ T := by simpa [Real.norm_eq_abs] using hT t ht
    exact abs_le.mp htT
  have hkE : IntegrableOn k E :=
    ((verticalReferenceKernel_continuous a).integrableOn_Icc).mono_set hET
  have herr := regularExterior_reference_vertical_errors_integrable
    F hc hs0 hs1 ξ hξ a
  have hkmin := verticalReferenceKernel_centered_interval_minimizes a h hh.le E hE
  have hbound := compensated_auxiliary_le_reference_errors
    g G k E I hE.1 hI herr.1 herr.2 hkE hkI hkmin
  rw [hU]
  simpa only [g, G, k, I, regularExteriorVerticalPotentialDifference,
    regularExteriorRotatedPotential, comparisonSegmentPotential] using hbound

/-- The actual auxiliary value tends uniformly to at most zero along
horizontal escape, independently of its positive height. -/
theorem regularVerticalAuxiliary_horizontal_decay_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a h : ℝ), 0 < h →
      regularVerticalAuxiliary F s ξ a h ≤
        C * Real.pi / Real.sqrt (1 + a ^ 2) := by
  obtain ⟨C, hC0, herror⟩ :=
    regularExterior_reference_vertical_errors_integral_le F hc hs0 hs1 ξ hξ
  refine ⟨C, hC0, ?_⟩
  intro a h hh
  exact (regularVerticalAuxiliary_le_reference_vertical_errors
    F hc hs0 hs1 ξ hξ a h hh).trans (herror a)

end SpringerLean
