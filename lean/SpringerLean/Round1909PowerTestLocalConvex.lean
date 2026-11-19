import SpringerLean.Round1908EvenLocalConvexCriterion

namespace SpringerLean

private theorem interpolationPowerTest_differentiable
    {a θ : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) :
    Differentiable ℝ (interpolationPowerTest a θ) := by
  let p := a + 2 * θ
  have hp : 1 ≤ p := by dsimp [p]; linarith
  have ha1 : 1 ≤ a := by linarith
  have ha2 : 1 ≤ a + 2 := by linarith
  have h1 := Real.differentiable_rpow_const hp
  have h2 := Real.differentiable_rpow_const ha1
  have h3 := Real.differentiable_rpow_const ha2
  change Differentiable ℝ
    (((fun x : ℝ => x ^ p) - fun x => (p * (1 - θ) / a) * x ^ a) -
      fun x => (p * θ / (a + 2)) * x ^ (a + 2))
  exact (h1.sub (h2.const_mul _)).sub (h3.const_mul _)

/-- The specific compensated interpolation test is convex on the
normalized projection interval [-1,1]. -/
theorem interpolationPowerTest_compensated_localConvex
    {a θ : ℝ} (ha : 4 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1)
      (fun x => interpolationPowerTest a θ |x| +
        ((a + 2 * θ) * θ * (1 - θ) * interpolationCurvatureConstant a) * x ^ 2) := by
  let c := (a + 2 * θ) * θ * (1 - θ) * interpolationCurvatureConstant a
  let f : ℝ → ℝ := fun x => interpolationPowerTest a θ x + c * x ^ 2
  have hhdiff := interpolationPowerTest_differentiable ha hθ0
  have hfdiff : Differentiable ℝ f :=
    hhdiff.add ((differentiable_id.pow 2).const_mul c)
  have hderiv_eq : deriv f = fun x =>
      deriv (interpolationPowerTest a θ) x + 2 * c * x := by
    funext x
    have h1 := (hhdiff x).hasDerivAt
    have h2 := ((hasDerivAt_id x).pow 2).const_mul c
    have h := h1.add h2
    have hh : HasDerivAt f
        (deriv (interpolationPowerTest a θ) x + 2 * c * x) x := by
      convert h using 1
      · funext y
        rfl
      · simp only [id_eq]
        ring
    exact hh.deriv
  have hfsecond (x : ℝ) (hx : 0 < x) :
      HasDerivAt (deriv f)
        (deriv (deriv (interpolationPowerTest a θ)) x + 2 * c) x := by
    have ha0 : a ≠ 0 := by linarith
    have ha2 : a + 2 ≠ 0 := by linarith
    have h1 := interpolationPowerTest_deriv_hasDerivAt
      (a := a) (θ := θ) hx ha0 ha2
    have h2 := (hasDerivAt_id x).const_mul (2 * c)
    have hD := h1.deriv
    rw [hderiv_eq, hD]
    convert h1.add h2 using 1
    · funext y
      rfl
    · ring
  have hfsecondDiff : DifferentiableOn ℝ (deriv f) (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (hfsecond x hx.1).differentiableAt.differentiableWithinAt
  have hcurv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ deriv (deriv f) x := by
    intro x hx
    have hh := interpolationPowerTest_second_deriv_lower ha hθ0 hθ1 hx.1 hx.2.le
    have hd := (hfsecond x hx.1).deriv
    dsimp [c] at hd
    rw [hd]
    nlinarith
  have hzero : deriv f 0 = 0 := by
    rw [hderiv_eq]
    have hp : 1 < a + 2 * θ := by linarith
    have ha1 : 1 < a := by linarith
    have ha2 : 1 < a + 2 := by linarith
    have h1 := Real.hasDerivAt_rpow_const (x := (0 : ℝ))
      (p := a + 2 * θ) (Or.inr hp.le)
    have h2 := Real.hasDerivAt_rpow_const (x := (0 : ℝ))
      (p := a) (Or.inr ha1.le)
    have h3 := Real.hasDerivAt_rpow_const (x := (0 : ℝ))
      (p := a + 2) (Or.inr ha2.le)
    have ha0 : a ≠ 0 := by linarith
    have ha2ne : a + 2 ≠ 0 := by linarith
    have h := (h1.sub (h2.const_mul ((a + 2 * θ) * (1 - θ) / a))).sub
      (h3.const_mul ((a + 2 * θ) * θ / (a + 2)))
    have hD : deriv (interpolationPowerTest a θ) 0 = 0 := by
      have hh : HasDerivAt (interpolationPowerTest a θ) 0 0 := by
        convert h using 1
        · funext x
          rfl
        · simp only [Real.zero_rpow (by linarith : a + 2 * θ - 1 ≠ 0),
            Real.zero_rpow (by linarith : a - 1 ≠ 0),
            Real.zero_rpow (by linarith : a + 2 - 1 ≠ 0)]
          ring
      exact hh.deriv
    change deriv (interpolationPowerTest a θ) 0 + 2 * c * 0 = 0
    rw [hD]
    ring
  have hconv := even_local_convex_of_second_deriv_nonneg f
    (fun x hx => hfdiff x) hfsecondDiff hzero hcurv
  convert hconv using 1
  funext x
  dsimp [f, c]
  rw [sq_abs]

end SpringerLean

#print axioms SpringerLean.interpolationPowerTest_compensated_localConvex
