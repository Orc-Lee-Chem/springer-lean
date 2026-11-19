import SpringerLean.Round29AuxHorizontalInfinity

open MeasureTheory Set

namespace SpringerLean

/-- The same reference-error bound includes the boundary height zero. -/
theorem regularVerticalAuxiliary_le_reference_vertical_errors_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 ≤ h) :
    regularVerticalAuxiliary F s ξ a h ≤
      ∫ t : ℝ,
        |regularExteriorRotatedPotential F s ξ
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| +
        |comparisonSegmentPotential
           ((a : ℂ) + (t : ℂ) * Complex.I) - verticalReferenceKernel a t| := by
  rcases eq_or_lt_of_le hh with rfl | hhpos
  · let g : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I)
    let G : ℝ → ℝ := fun t => comparisonSegmentPotential
      ((a : ℂ) + (t : ℂ) * Complex.I)
    let k : ℝ → ℝ := verticalReferenceKernel a
    have herr := regularExterior_reference_vertical_errors_integrable
      F hc hs0 hs1 ξ hξ a
    have hbound := compensated_auxiliary_le_reference_errors
      g G k (∅ : Set ℝ) ∅ (by simp) (by simp)
      herr.1 herr.2 (by simp) (by simp) (by simp)
    rw [regularVerticalAuxiliary_boundary]
    simpa [g, G, k, regularExteriorVerticalPotentialDifference,
      regularExteriorRotatedPotential, comparisonSegmentPotential] using hbound
  · exact regularVerticalAuxiliary_le_reference_vertical_errors
      F hc hs0 hs1 ξ hξ a h hhpos

/-- Uniform horizontal decay holds on the entire closed upper half-plane. -/
theorem regularVerticalAuxiliary_horizontal_decay_bound_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a h : ℝ), 0 ≤ h →
      regularVerticalAuxiliary F s ξ a h ≤
        C * Real.pi / Real.sqrt (1 + a ^ 2) := by
  obtain ⟨C, hC0, herror⟩ :=
    regularExterior_reference_vertical_errors_integral_le F hc hs0 hs1 ξ hξ
  refine ⟨C, hC0, ?_⟩
  intro a h hh
  exact (regularVerticalAuxiliary_le_reference_vertical_errors_nonneg
    F hc hs0 hs1 ξ hξ a h hh).trans (herror a)

end SpringerLean
