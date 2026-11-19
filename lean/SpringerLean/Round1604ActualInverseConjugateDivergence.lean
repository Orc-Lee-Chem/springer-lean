import SpringerLean.Round1603ActualInverseConjugateDerivative

open scoped ComplexConjugate

namespace SpringerLean

/-- The inverse-conjugate notation is exactly the paper's
`H/|H|²`, with `normSq H = |H|²`. -/
theorem inverseConjugate_eq_div_normSq (H : ℂ) :
    (conj H)⁻¹ = H / (Complex.normSq H : ℂ) := by
  rw [Complex.inv_def, Complex.conj_conj, Complex.normSq_conj,
    div_eq_mul_inv]
  rw [Complex.ofReal_inv]

/-- The actual phase flux field `H/|H|²`, written as
`(conj H)⁻¹`, has the required divergence away from zeros of H. -/
theorem actualHarmonic_inverseConjugate_divergence
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    (fderiv ℝ
      (fun w : ℂ => ((conj (actualHarmonic F w))⁻¹).re) z) (1:ℂ) +
    (fderiv ℝ
      (fun w : ℂ => ((conj (actualHarmonic F w))⁻¹).im) z) Complex.I =
      -2*(deriv (exteriorForwardGerm F) (conj z) /
        (actualHarmonic F z)^2).re := by
  let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
  have hQ : DifferentiableAt ℝ Q z :=
    actualHarmonic_inverseConjugate_differentiableAt F hc hz hH
  have hQR := (Complex.reCLM.hasFDerivAt (x := Q z)).comp z hQ.hasFDerivAt
  have hQI := (Complex.imCLM.hasFDerivAt (x := Q z)).comp z hQ.hasFDerivAt
  have hR := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ)) hQR.fderiv
  have hI := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hQI.fderiv
  have hcoords := actualHarmonic_inverseConjugate_gradient_coordinates
    F hc hz hH
  have hR' : (fderiv ℝ (fun w => (Q w).re) z) (1:ℂ) =
      ((fderiv ℝ Q z) (1:ℂ)).re := by
    change (fderiv ℝ (fun w => (Q w).re) z) (1:ℂ) = _ at hR
    simpa only [Complex.reCLM_apply, ContinuousLinearMap.comp_apply] using hR
  have hI' : (fderiv ℝ (fun w => (Q w).im) z) Complex.I =
      ((fderiv ℝ Q z) Complex.I).im := by
    change (fderiv ℝ (fun w => (Q w).im) z) Complex.I = _ at hI
    simpa only [Complex.imCLM_apply, ContinuousLinearMap.comp_apply] using hI
  rw [hR', hI', hcoords.1, hcoords.2]
  exact inverseConjugate_divergence_algebra
    (actualHarmonic F z)
    (deriv (exteriorForwardGerm F) (conj z)) hH

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inverseConjugate_divergence
#print axioms SpringerLean.inverseConjugate_eq_div_normSq
