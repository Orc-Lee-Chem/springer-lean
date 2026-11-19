import SpringerLean.Round1649WeightedDerivativeTransfer

namespace SpringerLean

/-- The exact actual bound used in the multiplier estimate:
|u| times the modulus gradient costs at most 2|u|+p/k. -/
theorem actualHarmonicPhase_weighted_modulus_gradient_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    |U z / y z| * ‖fderiv ℝ y z‖ ≤
      2*|U z / y z| + p/(k:ℝ) := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let p := Real.sqrt
    (((fderiv ℝ U z) (1:ℂ))^2+
     ((fderiv ℝ U z) Complex.I)^2)
  let q := |U z / y z|
  let Y := (y z)^(k-1)
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hy : 0 < y z := norm_pos_iff.mpr hH
  have hY : 0 < Y := pow_pos hy _
  have hq : 0 ≤ q := abs_nonneg _
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hqY : q ≤ Y :=
    actualHarmonicPhase_quotient_abs_le F k hk beta hbeta z hH
  have hweighted := actualHarmonic_weighted_fderiv_le_phase_gradient
    F hc k beta hbeta hz
  have htrans := weighted_derivative_transfer
    hkR hY hq hqY hp hweighted
  have hmod := actualHarmonic_modulus_fderiv_norm_le F hc hz hH
  have hmul := mul_le_mul_of_nonneg_left hmod hq
  exact hmul.trans htrans

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_weighted_modulus_gradient_le
