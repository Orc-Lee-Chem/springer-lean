import SpringerLean.Round1658ActualModulusGradientPairing

namespace SpringerLean

/-- The radial derivative of the actual filling modulus has exactly
the potential and mixed-gradient costs entered in the multiplier table. -/
theorem actualHarmonicPhase_radial_modulus_cost_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0) (a : ℝ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let u := U z/y z
    let yr := (fderiv ℝ y z) (z/‖z‖)
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let p := Real.sqrt (ux^2+uy^2)
    (-(k:ℝ)*a*yr*u^2) ≤
      2*(k:ℝ)*|a| * u^2+|a| * |u| * p := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let u := U z/y z
  let yr := (fderiv ℝ y z) (z/‖z‖)
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let L := ‖fderiv ℝ y z‖
  have hK : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hK0 : (k:ℝ) ≠ 0 := ne_of_gt hK
  have hrad := scalar_radial_fderiv_abs_le y hz0
  have hweighted := actualHarmonicPhase_weighted_modulus_gradient_le
    F hc k hk beta hbeta hz hH
  have hq : 0 ≤ |u| := abs_nonneg _
  have hsquare : u^2 = |u|^2 := (sq_abs u).symm
  have hL : |yr| * u^2 ≤ 2*u^2+|u| * p/(k:ℝ) := by
    have hw' : |u| * L ≤ 2*|u|+p/(k:ℝ) := hweighted
    have hw := mul_le_mul_of_nonneg_left hw' hq
    have hr := mul_le_mul_of_nonneg_right hrad (sq_nonneg u)
    calc
      |yr| * u^2 ≤ L*u^2 := hr
      _ = |u| * (|u| * L) := by rw [hsquare]; ring
      _ ≤ |u| * (2*|u|+p/(k:ℝ)) := hw
      _ = 2*u^2+|u| * p/(k:ℝ) := by rw [hsquare]; ring
  have hterm : -(a*yr) ≤ |a| * |yr| := by
    calc
      -(a*yr) ≤ |a*yr| := neg_le_abs _
      _ = |a| * |yr| := abs_mul _ _
  have hfactor : 0 ≤ (k:ℝ)*u^2 := by positivity
  have hstep := mul_le_mul_of_nonneg_left hterm hfactor
  have hfactor2 : 0 ≤ (k:ℝ)*|a| := by positivity
  have hstep2 := mul_le_mul_of_nonneg_left hL hfactor2
  dsimp only at hweighted ⊢
  calc
    -(k:ℝ)*a*yr*u^2 = ((k:ℝ)*u^2)*(-(a*yr)) := by ring
    _ ≤ ((k:ℝ)*u^2)*(|a| * |yr|) := hstep
    _ = ((k:ℝ)*|a|)*(|yr| * u^2) := by ring
    _ ≤ ((k:ℝ)*|a|)*(2*u^2+|u| * p/(k:ℝ)) := hstep2
    _ = 2*(k:ℝ)*|a| * u^2+|a| * |u| * p := by
      field_simp [hK0]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_radial_modulus_cost_le
