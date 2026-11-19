import SpringerLean.Round1593PhasePowerDerivative

namespace SpringerLean

theorem fderiv_real_const_mul_apply
    (f : ℂ → ℝ) (a : ℝ) (z u : ℂ) :
    (fderiv ℝ (fun w => a*f w) z) u =
      a*(fderiv ℝ f z u) := by
  change (fderiv ℝ (a • f) z) u = _
  rw [fderiv_const_smul_field]
  rfl

/-- Real directional derivative of the imaginary part of a complex
product with a constant added to the second factor. -/
theorem fderiv_im_product_one_add
    (W C : ℂ → ℂ) (z u : ℂ)
    (hW : DifferentiableAt ℝ W z) (hC : DifferentiableAt ℝ C z) :
    (fderiv ℝ (fun w => (W w*(1+C w)).im) z) u =
      ((fderiv ℝ W z u)*(1+C z)+W z*(fderiv ℝ C z u)).im := by
  have hplus := (hasFDerivAt_const (x := z) (1:ℂ)).add hC.hasFDerivAt
  have hprod := hW.hasFDerivAt.mul hplus
  have him := (Complex.imCLM.hasFDerivAt
    (x := W z*(1+C z))).comp z hprod
  have h := him.fderiv
  have hu := congrArg (fun L : ℂ →L[ℝ] ℝ => L u) h
  change (fderiv ℝ (fun w => (W w*(1+C w)).im) z) u = _ at hu
  simp only [Complex.imCLM_apply, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, zero_add, Pi.add_apply,
    smul_eq_mul] at hu
  rw [hu]
  congr 1
  ring

/-- The corresponding real-part derivative with a constant minus the
second factor. -/
theorem fderiv_re_product_one_sub
    (W C : ℂ → ℂ) (z u : ℂ)
    (hW : DifferentiableAt ℝ W z) (hC : DifferentiableAt ℝ C z) :
    (fderiv ℝ (fun w => (W w*(1-C w)).re) z) u =
      ((fderiv ℝ W z u)*(1-C z)-W z*(fderiv ℝ C z u)).re := by
  have hminus := (hasFDerivAt_const (x := z) (1:ℂ)).sub hC.hasFDerivAt
  have hprod := hW.hasFDerivAt.mul hminus
  have hre := (Complex.reCLM.hasFDerivAt
    (x := W z*(1-C z))).comp z hprod
  have h := hre.fderiv
  have hu := congrArg (fun L : ℂ →L[ℝ] ℝ => L u) h
  change (fderiv ℝ (fun w => (W w*(1-C w)).re) z) u = _ at hu
  simp only [Complex.reCLM_apply, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, neg_apply, zero_sub,
    Pi.sub_apply, smul_eq_mul] at hu
  rw [hu]
  congr 1
  ring

end SpringerLean

#print axioms SpringerLean.fderiv_im_product_one_add
#print axioms SpringerLean.fderiv_re_product_one_sub
#print axioms SpringerLean.fderiv_real_const_mul_apply
