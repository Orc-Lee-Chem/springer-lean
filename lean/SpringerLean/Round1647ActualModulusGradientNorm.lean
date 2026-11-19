import SpringerLean.Round1646ActualSigmaGradientIdentity
import Mathlib.Analysis.Calculus.FDeriv.Norm

namespace SpringerLean

/-- The real differential of the modulus of the actual filling has
operator norm at most the differential of the filling itself. -/
theorem actualHarmonic_modulus_fderiv_norm_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    ‖fderiv ℝ (fun w : ℂ => ‖actualHarmonic F w‖) z‖ ≤
      ‖fderiv ℝ (actualHarmonic F) z‖ := by
  have hfill := (actualHarmonic_hasFDerivAt_real F hc hz).differentiableAt
  have hnorm : DifferentiableAt ℝ (fun w : ℂ => ‖w‖)
      (actualHarmonic F z) :=
    differentiableAt_id.norm (𝕜 := ℂ) hH
  have hcomp := fderiv_fun_comp (x := z)
    (f := actualHarmonic F)
    (g := fun w : ℂ => ‖w‖) hnorm hfill
  calc
    ‖fderiv ℝ (fun w : ℂ => ‖actualHarmonic F w‖) z‖ =
      ‖(fderiv ℝ (fun w : ℂ => ‖w‖) (actualHarmonic F z)).comp
        (fderiv ℝ (actualHarmonic F) z)‖ := by
          exact congrArg norm hcomp
    _ ≤ ‖fderiv ℝ (fun w : ℂ => ‖w‖) (actualHarmonic F z)‖ *
      ‖fderiv ℝ (actualHarmonic F) z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (actualHarmonic F) z‖ := by
      rw [norm_fderiv_norm hnorm]
      ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_modulus_fderiv_norm_le
