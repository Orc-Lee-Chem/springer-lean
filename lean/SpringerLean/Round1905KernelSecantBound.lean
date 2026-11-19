import SpringerLean.Round1904InterpolationCurvatureUniform

namespace SpringerLean

noncomputable def interpolationCurvatureConstant (a : ℝ) : ℝ :=
  1 / (6 * (a - 2)) + 4 / (7 * (a - 2) ^ 2)

/-- Convexity of the shifted interpolation kernel on the parameter
interval [a,a+2]. This is the exact analytic premise consumed by the
secant lemma; all real exponent dependence is explicit. -/
theorem interpolationCurvatureKernel_shifted_convex
    {a t : ℝ} (ha : 4 ≤ a) (ht : 0 < t) (ht1 : t ≤ 1) :
    ConvexOn ℝ (Set.Icc a (a + 2))
      (fun k => interpolationCurvatureConstant a / 2 * k ^ 2 -
        interpolationCurvatureKernel t k) := by
  let L := interpolationCurvatureConstant a
  let f : ℝ → ℝ := fun k => L / 2 * k ^ 2 - interpolationCurvatureKernel t k
  have hfderiv (k : ℝ) :
      HasDerivAt f (L * k - deriv (interpolationCurvatureKernel t) k) k := by
    have h1 := ((hasDerivAt_id k).pow 2).const_mul (L / 2)
    have h2 := interpolationCurvatureKernel_hasDerivAt ht k
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · rw [h2.deriv]
      simp only [id_eq]
      ring
  have hfderiv_eq : deriv f =
      fun k => L * k - deriv (interpolationCurvatureKernel t) k := by
    funext k
    exact (hfderiv k).deriv
  have hfsecond (k : ℝ) :
      HasDerivAt (deriv f)
        (L - deriv (deriv (interpolationCurvatureKernel t)) k) k := by
    rw [hfderiv_eq]
    have h1 := (hasDerivAt_id k).const_mul L
    have h2 := interpolationCurvatureKernel_deriv_hasDerivAt ht k
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · rw [h2.deriv]
      ring
  have hfdiff : Differentiable ℝ f := fun k => (hfderiv k).differentiableAt
  have hfsecdiff : Differentiable ℝ (deriv f) :=
    fun k => (hfsecond k).differentiableAt
  apply convexOn_of_deriv2_nonneg' (convex_Icc a (a + 2))
    hfdiff.differentiableOn hfsecdiff.differentiableOn
  intro k hk
  change 0 ≤ deriv (deriv f) k
  rw [(hfsecond k).deriv]
  have hka : a ≤ k := hk.1
  have hL := interpolationCurvatureKernel_second_deriv_le ha hka ht ht1
  dsimp [L, interpolationCurvatureConstant]
  linarith

theorem interpolationCurvatureKernel_secant
    {a t θ : ℝ} (ha : 4 ≤ a) (ht : 0 < t) (ht1 : t ≤ 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) * interpolationCurvatureKernel t a +
        θ * interpolationCurvatureKernel t (a + 2) -
        interpolationCurvatureKernel t (a + 2 * θ) ≤
      2 * interpolationCurvatureConstant a * θ * (1 - θ) :=
  interpolation_secant_from_shifted_convex
    (interpolationCurvatureKernel t) a (interpolationCurvatureConstant a)
    θ hθ0 hθ1
    (interpolationCurvatureKernel_shifted_convex ha ht ht1)

end SpringerLean

#print axioms SpringerLean.interpolationCurvatureKernel_secant
