import SpringerLean.Round258GenericFaberEnergy

namespace SpringerLean

theorem polynomialReciprocalFactor_boundary_factor
    (F : ℂ → ℂ) (P : Polynomial ℂ) (N : ℕ)
    (hP : P.natDegree ≤ N) (θ : AddCircle (2 * Real.pi)) :
    P.eval (F (fourier 1 θ)) =
      fourier (N : ℤ) θ *
        polynomialReciprocalFactor F P N (fourier (-1) θ) :=
  reciprocal_factor_to_fourier_boundary F P N _
    (fun {u} hu => polynomialReciprocalFactor_eq_reciprocal_eval F P N hP hu) θ

theorem rescaleExterior_polynomialReciprocalFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (P : Polynomial ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (polynomialReciprocalFactor (rescaleExterior s F) P N)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hφ := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  unfold polynomialReciprocalFactor
  fun_prop

/-- Arbitrary finite polynomial area inequality for an actual regularized
map. Only the original function class and parameter/degree ranges remain;
the signed-area input is proved using the same actual omitted set. -/
theorem rescaleExterior_polynomial_negative_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (P : Polynomial ℂ) (N : ℕ) (hP : P.natDegree ≤ N) :
    let A := polynomialReciprocalFactor (rescaleExterior s F) P N
    (∑ j ∈ Finset.range N,
      ((j + 1 : ℕ) : ℝ) * ‖actualTaylorCoeff A (N + (j + 1))‖ ^ 2) ≤
      ∑ k ∈ Finset.range N,
        ((N : ℝ) - k) * ‖actualTaylorCoeff A k‖ ^ 2 := by
  dsimp only
  let A := polynomialReciprocalFactor (rescaleExterior s F) P N
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hA := rescaleExterior_polynomialReciprocalFactor_analyticOnNhd F hc hs0 P N
  apply analyticFactor_negative_energy_le A hR hA N
  let γ : ℝ → ℂ := fun θ =>
    fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  have hdiff : Differentiable ℝ γ :=
    faberBoundaryFactor_differentiable A hR hA (N : ℤ)
  have hIm (θ : ℝ) : deriv (fun t => (γ t).im) θ = (deriv γ θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        (hdiff θ).hasDerivAt).deriv
  have hnonneg : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t => (γ t).im) θ := by
    have h := faberPolynomial_actual_exterior_boundary_area_nonneg F hc hs0 hs1 P
    simpa only [γ, A, greenPolar_one_eq_fourier,
      polynomialReciprocalFactor_boundary_factor _ _ _ hP] using h
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (γ θ).re * (deriv γ θ).im
  convert hnonneg using 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  change (γ θ).re * (deriv γ θ).im =
    (γ θ).re * deriv (fun t => (γ t).im) θ
  rw [hIm]

end SpringerLean
