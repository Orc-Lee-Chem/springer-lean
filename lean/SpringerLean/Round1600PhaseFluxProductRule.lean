import SpringerLean.Round1599PhaseFluxCancellation

namespace SpringerLean

/-- Cartesian product rule for the first energy flux
`J_P = chi * U * grad U`. This version only assumes the displayed
first and second directional derivatives exist at the point. -/
theorem phaseFluxP_divergence_product_rule
    (chi U : ℂ → ℝ) (z : ℂ)
    (hchi : DifferentiableAt ℝ chi z)
    (hU : DifferentiableAt ℝ U z)
    (hUx : DifferentiableAt ℝ
      (fun w => (fderiv ℝ U w) (1:ℂ)) z)
    (hUy : DifferentiableAt ℝ
      (fun w => (fderiv ℝ U w) Complex.I) z) :
    (fderiv ℝ
      (fun w => chi w*U w*(fderiv ℝ U w) (1:ℂ)) z) (1:ℂ) +
    (fderiv ℝ
      (fun w => chi w*U w*(fderiv ℝ U w) Complex.I) z) Complex.I =
      chi z *
        ((fderiv ℝ U z (1:ℂ))^2 +
         (fderiv ℝ U z Complex.I)^2) +
      chi z * U z *
        ((fderiv ℝ (fun w => (fderiv ℝ U w) (1:ℂ)) z) (1:ℂ) +
         (fderiv ℝ (fun w => (fderiv ℝ U w) Complex.I) z) Complex.I) +
      U z *
        ((fderiv ℝ chi z (1:ℂ))*(fderiv ℝ U z (1:ℂ)) +
         (fderiv ℝ chi z Complex.I)*(fderiv ℝ U z Complex.I)) := by
  have hchiU : DifferentiableAt ℝ (fun w => chi w*U w) z :=
    hchi.mul hU
  have hinner := fderiv_fun_mul hchi hU
  have hx := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ))
    (fderiv_fun_mul hchiU hUx)
  have hy := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
    (fderiv_fun_mul hchiU hUy)
  rw [hinner] at hx hy
  simp only [add_apply, smul_apply, smul_eq_mul] at hx hy
  rw [hx, hy]
  ring

end SpringerLean

#print axioms SpringerLean.phaseFluxP_divergence_product_rule
