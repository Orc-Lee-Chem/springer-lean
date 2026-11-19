import SpringerLean.Round1607ActualPhaseFluxP

namespace SpringerLean
noncomputable section

/-- The paper's multiplier time on the punctured source disk and away
from zeros of the actual filling. -/
def actualHarmonicMultiplierTime (F : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℝ :=
  (k:ℝ)*(1-‖z‖)/‖actualHarmonic F z‖

theorem actualHarmonic_norm_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    DifferentiableAt ℝ (fun w => ‖actualHarmonic F w‖) z :=
  (actualHarmonic_hasFDerivAt_real F hc hz).differentiableAt.norm
    (𝕜 := ℂ) hH

theorem source_radius_differentiableAt
    {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun w : ℂ => ‖w‖) z :=
  differentiableAt_id.norm (𝕜 := ℂ) hz

theorem actualHarmonicMultiplierTime_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (hH : actualHarmonic F z ≠ 0) :
    DifferentiableAt ℝ (actualHarmonicMultiplierTime F k) z := by
  have hr := source_radius_differentiableAt hz0
  have hy := actualHarmonic_norm_differentiableAt F hc hz hH
  have hnum : DifferentiableAt ℝ
      (fun w : ℂ => (k:ℝ)*(1-‖w‖)) z :=
    ((differentiableAt_const (x := z) (1:ℝ)).sub hr).const_mul (k:ℝ)
  have hy0 : ‖actualHarmonic F z‖ ≠ 0 := norm_ne_zero_iff.mpr hH
  change DifferentiableAt ℝ
    (fun w : ℂ => ((k:ℝ)*(1-‖w‖))*‖actualHarmonic F w‖⁻¹) z
  exact hnum.mul (hy.inv hy0)

end
end SpringerLean

#print axioms SpringerLean.actualHarmonic_norm_differentiableAt
#print axioms SpringerLean.actualHarmonicMultiplierTime_differentiableAt
