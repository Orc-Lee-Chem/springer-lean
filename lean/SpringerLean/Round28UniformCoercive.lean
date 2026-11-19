import SpringerLean.Round28ActualPotentialContinuous

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual regularized rotated potential exceeds any fixed level at
both vertical ends, with a threshold independent of the horizontal line. -/
theorem regularExterior_rotated_potential_vertical_uniform_coercive
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (R : ℝ) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (a t : ℝ), T ≤ |t| →
      R < regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨M, hM0, hM⟩ :=
    regularExterior_boundary_curve_norm_bounded F hc hs0 hs1
  let T : ℝ := max 0 (M + Real.exp (R + 1)) + 1
  refine ⟨T, by dsimp [T]; linarith [le_max_left (0 : ℝ) (M + Real.exp (R + 1))], ?_⟩
  intro a t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  have him : z.im = t := by simp [z]
  have htnorm : |t| ≤ ‖ξ * z‖ := by
    rw [norm_mul, hξ, one_mul]
    simpa only [him] using Complex.abs_im_le_norm z
  have hlarge : Real.exp (R + 1) ≤ ‖ξ * z‖ - M := by
    dsimp [T] at ht
    have hMexp : M + Real.exp (R + 1) ≤
        max 0 (M + Real.exp (R + 1)) := le_max_right _ _
    linarith
  have hw : M < ‖ξ * z‖ := by linarith [Real.exp_pos (R + 1)]
  have hpot := regularExterior_boundary_potential_log_lower
    F hc hs0 hs1 hM hw
  have hlog : R + 1 ≤ Real.log (‖ξ * z‖ - M) := by
    rw [← Real.log_exp (R + 1)]
    exact Real.log_le_log (Real.exp_pos (R + 1)) hlarge
  rw [regularExterior_rotated_potential_eq F s ξ hξ z]
  exact lt_of_lt_of_le (by linarith) (hlog.trans hpot)

end SpringerLean