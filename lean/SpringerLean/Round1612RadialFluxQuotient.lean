import SpringerLean.Round1611RadialFluxProductRule

namespace SpringerLean

/-- Radial flux with an arbitrary differentiable scalar multiplier. -/
theorem radialFlux_divergence_quotient
    (phi U y : ℂ → ℝ) (z : ℂ)
    (hphi : DifferentiableAt ℝ phi z)
    (hU : DifferentiableAt ℝ U z)
    (hy : DifferentiableAt ℝ y z)
    (hz : z ≠ 0) (hy0 : y z ≠ 0) :
    let er : ℂ := z/‖z‖
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((phi w*(U w)^2/y w)*w.im)/‖w‖) z) Complex.I =
      (phi z*(U z)^2/y z)/‖z‖ +
      ((fderiv ℝ phi z) er*(U z)^2/y z) +
      2*phi z*U z*(fderiv ℝ U z) er/y z -
      phi z*(U z)^2*(fderiv ℝ y z) er/(y z)^2 := by
  let a : ℂ → ℝ := fun w => phi w*(U w)^2/y w
  have hU2 : DifferentiableAt ℝ (fun w => (U w)^2) z := hU.pow 2
  have hnum : DifferentiableAt ℝ (fun w => phi w*(U w)^2) z :=
    hphi.mul hU2
  have ha : DifferentiableAt ℝ a z := by
    change DifferentiableAt ℝ
      (fun w => (phi w*(U w)^2)*(y w)⁻¹) z
    exact hnum.mul (hy.inv hy0)
  have hrad := radialFlux_divergence_product_rule a z ha hz
  let er : ℂ := z/‖z‖
  have hquot := fderiv_ratio_apply_of_denominator_ne_zero
    (fun w => phi w*(U w)^2) y z er hnum hy hy0
  have hmul := congrArg (fun L : ℂ →L[ℝ] ℝ => L er)
    (fderiv_fun_mul hphi hU2)
  have hpow := congrArg (fun L : ℂ →L[ℝ] ℝ => L er)
    (hU.hasFDerivAt.pow 2).fderiv
  simp only [add_apply, smul_apply, smul_eq_mul] at hmul hpow
  rw [hpow] at hmul
  dsimp only [a] at hrad
  dsimp only [er] at hquot hmul
  rw [hquot, hmul] at hrad
  dsimp only [er]
  convert hrad using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.radialFlux_divergence_quotient
