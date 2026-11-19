import SpringerLean.Round691AngularTopDual

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- The actual top value bounds a candidate in ANY angular turn.  The
threshold is obtained for the same actual F, so no modulo representative
or additional comparison premise is needed.  All masses are raw lengths. -/
theorem actualAngularTopValue_candidate_le_any_turn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (q : ℝ) (E : Set ℝ) (hEm : MeasurableSet E)
    (hsub : E ⊆ Ioc q (q+2*Real.pi))
    (hmass : volume E = ENNReal.ofReal (2*h)) :
    (∫ t in E, (c*actualHarmonic F (circleMap 0 r t)).re) ≤
      actualAngularTopValue F c r h := by
  obtain ⟨ell, hell, hval⟩ :=
    actualAngularTopValue_exists_bounded_threshold F hc c hr0 hr1 hh0 hhpi
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hmass, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hu := actualHarmonic_angular_setIntegral_le_threshold F hc c
    hr0 hr1 ell q E hEm hsub
  rw [hreal] at hu
  rw [hval]
  convert hu using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.actualAngularTopValue_candidate_le_any_turn
