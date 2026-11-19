import SpringerLean.Round08Omitted

open scoped ComplexConjugate

namespace SpringerLean

/-- Real differential model of `z ↦ z+g(conj z)` at a point with complex
derivative `c=g'(conj z)`. -/
noncomputable def harmonicRealLinearMap (c : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  (1 : ℂ →ₗ[ℝ] ℂ) +
    (c • (1 : ℂ →ₗ[ℝ] ℂ)).comp Complex.conjAe.toLinearMap

@[simp] theorem harmonicRealLinearMap_apply (c v : ℂ) :
    harmonicRealLinearMap c v = v + c * conj v := by
  simp [harmonicRealLinearMap]

/-- Signed real Jacobian of the harmonic filling. It can be negative. -/
theorem harmonicRealLinearMap_det (c : ℂ) :
    (harmonicRealLinearMap c).det = 1 - ‖c‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have hm : (harmonicRealLinearMap c).toMatrix
      Complex.basisOneI Complex.basisOneI =
      !![1 + c.re, c.im; c.im, 1 - c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, harmonicRealLinearMap_apply,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [hm, Matrix.det_fin_two_of]
  calc
    (1 + c.re) * (1 - c.re) - c.im * c.im =
        1 - (c.re ^ 2 + c.im ^ 2) := by ring
    _ = 1 - ‖c‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring

/-- The real Fréchet derivative of the actual regular harmonic filling. -/
theorem regularHarmonic_hasFDerivAt_real
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasFDerivAt (regularHarmonic s F)
      ((1 : ℂ →L[ℝ] ℂ) +
        ((deriv (regularForwardGerm s F) (conj z)) •
          (1 : ℂ →L[ℝ] ℂ)).comp Complex.conjCLE.toContinuousLinearMap) z := by
  have hzc : conj z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  have ha : AnalyticAt ℂ (regularForwardGerm s F) (conj z) := by
    rw [regularForwardGerm_eq_actual s hs0 F]
    exact exteriorForwardGerm_analyticOnNhd_unitBall
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1) (conj z) hzc
  have hg : HasDerivAt (regularForwardGerm s F)
      (deriv (regularForwardGerm s F) (conj z)) (conj z) :=
    ha.differentiableAt.hasDerivAt
  have hconj : HasFDerivAt (fun u : ℂ => conj u)
      Complex.conjCLE.toContinuousLinearMap z := by
    convert (Complex.conjCLE.hasFDerivAt (x := z)) using 1
    funext u
    simp
  have hcomp := hg.complexToReal_fderiv.comp z hconj
  have hsum := (hasFDerivAt_id z).add hcomp
  convert hsum using 1
  funext u
  simp [regularHarmonic, Function.comp_def, Pi.add_apply]

/-- Signed Jacobian of the actual regularized filling at each interior
point, without assuming that the filling is injective or orientation preserving. -/
theorem regularHarmonic_fderiv_det
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (fderiv ℝ (regularHarmonic s F) z).det =
      1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 := by
  let c : ℂ := deriv (regularForwardGerm s F) (conj z)
  have hder := (regularHarmonic_hasFDerivAt_real F hc hs0 hs1 hz).fderiv
  rw [hder]
  have heq :
      ((1 : ℂ →L[ℝ] ℂ) +
        (c • (1 : ℂ →L[ℝ] ℂ)).comp Complex.conjCLE.toContinuousLinearMap).toLinearMap =
      harmonicRealLinearMap c := by
    ext v
    simp [harmonicRealLinearMap]
  change
    ((1 : ℂ →L[ℝ] ℂ) +
      (c • (1 : ℂ →L[ℝ] ℂ)).comp Complex.conjCLE.toContinuousLinearMap).toLinearMap.det =
      1 - ‖c‖ ^ 2
  rw [heq]
  exact harmonicRealLinearMap_det c

/-- The weighted disk integral retains the signed Jacobian. This theorem
does not identify it with the omitted set; that is the remaining Stokes step. -/
theorem regularHarmonic_weighted_signedJacobian_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖regularHarmonic s F z‖ ^ m *
        (fderiv ℝ (regularHarmonic s F) z).det ∂MeasureTheory.volume) =
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖regularHarmonic s F z‖ ^ m *
        (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2) ∂MeasureTheory.volume) := by
  apply MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro z hz
  have hz' : ‖z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [Function.comp_apply] using
    congrArg (fun t : ℝ => ‖regularHarmonic s F z‖ ^ m * t)
      (regularHarmonic_fderiv_det F hc hs0 hs1 hz')

end SpringerLean
