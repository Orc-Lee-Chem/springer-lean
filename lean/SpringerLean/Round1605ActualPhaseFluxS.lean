import SpringerLean.Round1604ActualInverseConjugateDivergence

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual phase flux product rule away from zeros of H.  The
multiplier `sigma` is an arbitrary differentiable real function here;
the paper's piecewise affine `sigma(t)` will be substituted later. -/
theorem actualHarmonic_phaseFluxS_divergence
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) (sigma : ℂ → ℝ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0)
    (hsigma : DifferentiableAt ℝ sigma z) :
    let U := actualHarmonicPhaseField F k beta
    let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*(Q w).re) z) (1:ℂ) +
    (fderiv ℝ
      (fun w => sigma w*(U w)^2*(Q w).im) z) Complex.I =
      2*sigma z*U z *
        ((Q z).re*(fderiv ℝ U z (1:ℂ)) +
         (Q z).im*(fderiv ℝ U z Complex.I)) +
      (U z)^2 *
        ((Q z).re*(fderiv ℝ sigma z (1:ℂ)) +
         (Q z).im*(fderiv ℝ sigma z Complex.I) -
         2*sigma z *
           (deriv (exteriorForwardGerm F) (conj z) /
             (actualHarmonic F z)^2).re) := by
  let U := actualHarmonicPhaseField F k beta
  let Q : ℂ → ℂ := fun w => (conj (actualHarmonic F w))⁻¹
  have hU : DifferentiableAt ℝ U z :=
    (actualHarmonicPhaseField_hasFDerivAt F hc k beta hz).differentiableAt
  have hQ : DifferentiableAt ℝ Q z :=
    actualHarmonic_inverseConjugate_differentiableAt F hc hz hH
  have hQx : DifferentiableAt ℝ (fun w => (Q w).re) z :=
    Complex.reCLM.differentiableAt.comp z hQ
  have hQy : DifferentiableAt ℝ (fun w => (Q w).im) z :=
    Complex.imCLM.differentiableAt.comp z hQ
  have hprod := phaseFluxS_divergence_product_rule
    sigma U (fun w => (Q w).re) (fun w => (Q w).im) z
    hsigma hU hQx hQy
  have hdiv := actualHarmonic_inverseConjugate_divergence F hc hz hH
  dsimp only at hprod ⊢
  rw [hdiv] at hprod
  nlinarith [hprod]

end SpringerLean

#print axioms SpringerLean.actualHarmonic_phaseFluxS_divergence
