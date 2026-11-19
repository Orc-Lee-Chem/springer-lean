import SpringerLean.Round30ActualSemicircleComplement
import SpringerLean.Round27ActualTruncation

open MeasureTheory Set

namespace SpringerLean

/-- The actual positive-height auxiliary equals the unshifted finite-window
complement for any genuine optimizer contained in that window. -/
theorem regularVerticalAuxiliary_eq_finiteComplement_of_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h T : ℝ) (hh : 0 < h)
    (E : Set ℝ) (hE : E ∈ verticalFeasible h)
    (hmin : (∫ t in E, regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h))
    (hT : h ≤ T) (hES : E ⊆ Icc (-T) T) :
    regularVerticalAuxiliary F s ξ a h =
      regularVerticalFiniteComplement F s ξ a h T 0 E := by
  have h := regularVerticalAuxiliary_finite_complements_of_minimizer
    F hc hs0 hs1 ξ hξ a h hh E hE hmin T hT hES
  simpa only [regularVerticalFiniteComplement, add_zero] using h

end SpringerLean