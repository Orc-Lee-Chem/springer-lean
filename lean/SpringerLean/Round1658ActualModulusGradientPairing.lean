import SpringerLean.Round1657ScalarGradientDotBound

namespace SpringerLean

/-- The exact actual paired-gradient cost required by the chi and
sigma cutoff derivatives in the local multiplier estimate. -/
theorem actualHarmonicPhase_modulus_gradient_pairing_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let p := Real.sqrt (ux^2+uy^2)
    |(U z/y z)*
      ((fderiv ℝ y z) (1:ℂ)*ux+
       (fderiv ℝ y z) Complex.I*uy)| ≤
      (2*|U z/y z| + p/(k:ℝ))*p := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let u := U z/y z
  have hcs := scalar_fderiv_dot_gradient_abs_le y z ux uy
  have hmod := actualHarmonicPhase_weighted_modulus_gradient_le
    F hc k hk beta hbeta hz hH
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  calc
    |u*((fderiv ℝ y z) (1:ℂ)*ux+
       (fderiv ℝ y z) Complex.I*uy)| =
      |u| * |(fderiv ℝ y z) (1:ℂ)*ux+
       (fderiv ℝ y z) Complex.I*uy| := abs_mul _ _
    _ ≤ |u| * (‖fderiv ℝ y z‖*p) :=
      mul_le_mul_of_nonneg_left hcs (abs_nonneg u)
    _ = (|u| * ‖fderiv ℝ y z‖)*p := by ring
    _ ≤ (2*|u| + p/(k:ℝ))*p :=
      mul_le_mul_of_nonneg_right hmod hp

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_modulus_gradient_pairing_le
