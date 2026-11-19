import SpringerLean.Round1602InverseConjugateDivergenceAlgebra

open scoped ComplexConjugate

namespace SpringerLean

theorem actualHarmonic_inverseConjugate_differentiableAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    DifferentiableAt ℝ
      (fun w : ℂ => (conj (actualHarmonic F w))⁻¹) z := by
  have hconjH : conj (actualHarmonic F z) ≠ 0 := by
    intro hzero
    apply hH
    have hzero' := congrArg conj hzero
    simpa using hzero'
  have hbase := actualHarmonic_hasFDerivAt_real F hc hz
  have hconj := (Complex.conjCLE.hasFDerivAt
    (x := actualHarmonic F z)).comp z hbase
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hconjH).comp z hconj
  have hfun : (fun w : ℂ => (conj (actualHarmonic F w))⁻¹) =
      Inv.inv ∘ Complex.conjCLE ∘ actualHarmonic F := by
    funext w
    simp [Function.comp_def]
  rw [hfun]
  exact hinv.differentiableAt

/-- The actual inverse-conjugate field has explicit Cartesian first
derivatives away from zeros of the harmonic filling. -/
theorem actualHarmonic_inverseConjugate_gradient_coordinates
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    (fderiv ℝ
      (fun w : ℂ => (conj (actualHarmonic F w))⁻¹) z) (1:ℂ) =
      -(conj (1+deriv (exteriorForwardGerm F) (conj z))) /
        (conj (actualHarmonic F z))^2 ∧
    (fderiv ℝ
      (fun w : ℂ => (conj (actualHarmonic F w))⁻¹) z) Complex.I =
      -(conj (Complex.I*(1-deriv (exteriorForwardGerm F) (conj z)))) /
        (conj (actualHarmonic F z))^2 := by
  have hconjH : conj (actualHarmonic F z) ≠ 0 := by
    intro hzero
    apply hH
    have hzero' := congrArg conj hzero
    simpa using hzero'
  have hbase := actualHarmonic_hasFDerivAt_real F hc hz
  have hconj := (Complex.conjCLE.hasFDerivAt
    (x := actualHarmonic F z)).comp z hbase
  have hinv := (hasFDerivAt_inv' (𝕜 := ℝ) hconjH).comp z hconj
  have h := hinv.fderiv
  have hfun : (fun w : ℂ => (conj (actualHarmonic F w))⁻¹) =
      Inv.inv ∘ Complex.conjCLE ∘ actualHarmonic F := by
    funext w
    simp [Function.comp_def]
  constructor
  · have hx := congrArg (fun L : ℂ →L[ℝ] ℂ => L (1:ℂ)) h
    rw [hfun, hx]
    simp [ContinuousLinearMap.comp_apply, div_eq_mul_inv,
      pow_two, mul_assoc]
    ring
  · have hy := congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) h
    rw [hfun, hy]
    simp [ContinuousLinearMap.comp_apply, Complex.conj_I,
      div_eq_mul_inv, pow_two, mul_assoc]
    ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inverseConjugate_gradient_coordinates
#print axioms SpringerLean.actualHarmonic_inverseConjugate_differentiableAt
