import SpringerLean.Round1658ActualModulusGradientPairing

namespace SpringerLean

/-- The chi-cutoff modulus-gradient term has exactly the mixed and
quadratic-gradient costs printed in B and D. -/
theorem actualHarmonicPhase_chi_gradient_cost_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) (cp : ℝ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k z
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    let u := U z/y z
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let p := Real.sqrt (ux^2+uy^2)
    (-b*cp*t*u*((fderiv ℝ y z) (1:ℂ)*ux+
      (fderiv ℝ y z) Complex.I*uy)) ≤
      2*b*t*|cp| * |u| * p+(b/(k:ℝ))*t*|cp| * p^2 := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k z
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  let u := U z/y z
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let pair := u*((fderiv ℝ y z) (1:ℂ)*ux+
    (fderiv ℝ y z) Complex.I*uy)
  have hK : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hKm1 : (0:ℝ) < (k:ℝ)-1 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hpair := actualHarmonicPhase_modulus_gradient_pairing_le
    F hc k (by omega) beta hbeta hz hH
  have hterm : -cp*pair ≤ |cp| * |pair| := by
    calc
      -cp*pair = -(cp*pair) := by ring
      _ ≤ |cp*pair| := neg_le_abs _
      _ = |cp| * |pair| := abs_mul _ _
  have hfac : 0 ≤ b*t := mul_nonneg hb ht
  have hstep := mul_le_mul_of_nonneg_left hterm hfac
  have hfac2 : 0 ≤ b*t*|cp| := by positivity
  have hstep2 := mul_le_mul_of_nonneg_left hpair hfac2
  have hlocal : -b*cp*t*pair ≤
      2*b*t*|cp| * |u| * p+(b/(k:ℝ))*t*|cp| * p^2 := by
    calc
      -b*cp*t*pair = (b*t)*(-cp*pair) := by ring
      _ ≤ (b*t)*(|cp| * |pair|) := hstep
      _ = (b*t*|cp|)*|pair| := by ring
      _ ≤ (b*t*|cp|)*((2*|u|+p/(k:ℝ))*p) := hstep2
      _ = 2*b*t*|cp| * |u| * p+(b/(k:ℝ))*t*|cp| * p^2 := by
        ring
  simpa only [pair, mul_assoc] using hlocal

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_chi_gradient_cost_le
