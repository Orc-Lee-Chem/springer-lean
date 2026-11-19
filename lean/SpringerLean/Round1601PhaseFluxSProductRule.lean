import SpringerLean.Round1600PhaseFluxProductRule

namespace SpringerLean

/-- Product rule for the phase flux `J_S = sigma * U^2 * Q`, where
`Q` will later be the actual field `H/|H|^2`. The denominators and
their derivatives are isolated in `Q`. -/
theorem phaseFluxS_divergence_product_rule
    (sigma U Qx Qy : ℂ → ℝ) (z : ℂ)
    (hsigma : DifferentiableAt ℝ sigma z)
    (hU : DifferentiableAt ℝ U z)
    (hQx : DifferentiableAt ℝ Qx z)
    (hQy : DifferentiableAt ℝ Qy z) :
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*Qx w) z) (1:ℂ) +
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*Qy w) z) Complex.I =
      2*sigma z*U z *
        (Qx z*(fderiv ℝ U z (1:ℂ)) +
         Qy z*(fderiv ℝ U z Complex.I)) +
      (U z)^2 *
        (Qx z*(fderiv ℝ sigma z (1:ℂ)) +
         Qy z*(fderiv ℝ sigma z Complex.I) +
         sigma z *
          ((fderiv ℝ Qx z (1:ℂ))+
           (fderiv ℝ Qy z Complex.I))) := by
  have hUsq : DifferentiableAt ℝ (fun w => (U w)^2) z := hU.pow 2
  have hcoef : DifferentiableAt ℝ (fun w => sigma w*(U w)^2) z :=
    hsigma.mul hUsq
  have hsq := (hU.hasFDerivAt.pow 2).fderiv
  have hinner := fderiv_fun_mul hsigma hUsq
  have hx := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ))
    (fderiv_fun_mul hcoef hQx)
  have hy := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
    (fderiv_fun_mul hcoef hQy)
  rw [hinner] at hx hy
  simp only [add_apply, smul_apply, smul_eq_mul] at hx hy
  have hsqx := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ)) hsq
  have hsqy := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hsq
  simp only [smul_apply, smul_eq_mul] at hsqx hsqy
  rw [hsqx] at hx
  rw [hsqy] at hy
  rw [hx, hy]
  ring

end SpringerLean

#print axioms SpringerLean.phaseFluxS_divergence_product_rule
