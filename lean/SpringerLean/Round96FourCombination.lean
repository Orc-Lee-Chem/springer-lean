import SpringerLean.Round95FourthRow

namespace SpringerLean

/-- The actual polynomial used for the four-vector Faber area test. -/
noncomputable def fourthFaberCombinationPolynomial
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ : ℂ) : Polynomial ℂ :=
  thirdFaberCombinationPolynomial G α₁ α₂ α₃ +
    Polynomial.C α₄ * fourthFaberPolynomial G

/-- Reciprocal factor of the same polynomial, with leading frequency four. -/
noncomputable def fourthFaberCombinationFactor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ : ℂ) (u : ℂ) : ℂ :=
  u * thirdFaberCombinationFactor G α₁ α₂ α₃ u +
    α₄ * fourthFaberFactor G u

theorem fourthFaberCombinationFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (α₁ α₂ α₃ α₄ : ℂ) :
    AnalyticOnNhd ℂ
      (fourthFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃ α₄)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hthree := thirdFaberCombinationFactor_analyticOnNhd
    F hc hs0 α₁ α₂ α₃ u hu
  have hfour := rescaleExterior_fourthFaberFactor_analyticOnNhd
    F hc hs0 u hu
  change AnalyticAt ℂ (fourthFaberFactor (rescaleExterior s F)) u at hfour
  change AnalyticAt ℂ (fun x : ℂ =>
    x * thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃ x +
      α₄ * fourthFaberFactor (rescaleExterior s F) x) u
  exact (analyticAt_id.mul hthree).add (analyticAt_const.mul hfour)

theorem fourthFaberCombinationPolynomial_boundary_factor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ : ℂ)
    (θ : AddCircle (2 * Real.pi)) :
    (fourthFaberCombinationPolynomial G α₁ α₂ α₃ α₄).eval
        (G (fourier 1 θ)) =
      fourier 4 θ *
        fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ (fourier (-1) θ) := by
  let u : ℂ := fourier (-1) θ
  have h43 : fourier 4 θ * u = fourier 3 θ := by
    change fourier 4 θ * fourier (-1) θ = fourier 3 θ
    rw [← fourier_add]
    norm_num
  simp only [fourthFaberCombinationPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    thirdFaberCombinationPolynomial_boundary_factor,
    fourthFaberPolynomial_boundary_factor]
  change fourier 3 θ * thirdFaberCombinationFactor G α₁ α₂ α₃ u +
      α₄ * (fourier 4 θ * fourthFaberFactor G u) =
    fourier 4 θ * (u * thirdFaberCombinationFactor G α₁ α₂ α₃ u +
      α₄ * fourthFaberFactor G u)
  rw [← h43]
  ring

/-- Every four-vector Faber combination has nonnegative actual signed
boundary area. The polynomial itself need not be univalent. -/
theorem fourthFaberCombination_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) :
    let A := fourthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 4 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (fourier 4 (t : AddCircle (2 * Real.pi)) *
            A (fourier (-1) (t : AddCircle (2 * Real.pi)))).im) θ := by
  dsimp only
  let G := rescaleExterior s F
  let P := fourthFaberCombinationPolynomial G α₁ α₂ α₃ α₄
  have h := faberPolynomial_actual_exterior_boundary_area_nonneg
    F hc hs0 hs1 P
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ((fourthFaberCombinationPolynomial
      (rescaleExterior s F) α₁ α₂ α₃ α₄).eval
      (rescaleExterior s F (greenPolar 1 θ))).re *
      deriv (fun t : ℝ =>
        ((fourthFaberCombinationPolynomial
          (rescaleExterior s F) α₁ α₂ α₃ α₄).eval
          (rescaleExterior s F (greenPolar 1 t))).im) θ at h
  simpa only [greenPolar_one_eq_fourier,
    fourthFaberCombinationPolynomial_boundary_factor] using h

/-- Actual four-vector boundary area is the limit of finite Fourier areas. -/
theorem fourthFaberCombination_boundary_area_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) :
    let A := fourthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄
    let γn : ℕ → ℝ → ℂ := fun M θ =>
      fourier 4 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff A j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
    let γ : ℝ → ℂ := fun θ =>
      fourier 4 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
    Filter.Tendsto
      (fun M => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γn M θ).re * deriv (fun t => (γn M t).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  dsimp only
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  exact faberBoundaryFactor_oriented_integral_tendsto
    _ hR (fourthFaberCombinationFactor_analyticOnNhd
      F hc hs0 α₁ α₂ α₃ α₄) 4

/-- Green area bounds the first four negative Fourier modes of every
four-vector actual Faber combination. -/
theorem fourthFaberCombination_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) :
    let A := fourthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄
    ‖actualTaylorCoeff A 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 8‖ ^ 2 ≤
      4 * ‖actualTaylorCoeff A 0‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 1‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 2‖ ^ 2 +
        ‖actualTaylorCoeff A 3‖ ^ 2 := by
  dsimp only
  let A := fourthFaberCombinationFactor
    (rescaleExterior s F) α₁ α₂ α₃ α₄
  let γ : ℝ → ℂ := fun θ =>
    fourier 4 (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hAdiff : Differentiable ℝ γ := by
    simpa only [γ, A] using
      (faberBoundaryFactor_differentiable A hR
        (fourthFaberCombinationFactor_analyticOnNhd
          F hc hs0 α₁ α₂ α₃ α₄) 4)
  have hIm (θ : ℝ) : deriv (fun t => (γ t).im) θ =
      (deriv γ θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        (hAdiff θ).hasDerivAt).deriv
  have hIeq : I = ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t => (γ t).im) θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    simpa only using congrArg (fun x : ℝ => (γ θ).re * x) (hIm θ).symm
  have hnonneg : 0 ≤ I := by
    rw [hIeq]
    simpa only [γ, A] using
      fourthFaberCombination_boundary_area_nonneg
        F hc hs0 hs1 α₁ α₂ α₃ α₄
  have hlim : Filter.Tendsto
      (fun M => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (4 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2))
      Filter.atTop (nhds I) := by
    simpa only [fourthFaberFiniteBoundary_oriented_area, I, γ, A] using
      (fourthFaberCombination_boundary_area_tendsto
        F hc hs0 hs1 α₁ α₂ α₃ α₄)
  let B : ℝ :=
    4 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      ‖actualTaylorCoeff A 3‖ ^ 2 -
      (‖actualTaylorCoeff A 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 8‖ ^ 2)
  have hupper : I ≤ Real.pi * B :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨8, by
      intro M hM
      exact mul_le_mul_of_nonneg_left
        (fourthFaberFiniteSignedEnergy_le_firstFour
          (actualTaylorCoeff A) M hM) Real.pi_pos.le⟩)
  have hB : 0 ≤ B := by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  dsimp [B] at hB
  linarith

/-- Taylor extraction respects the two analytic summands in the actual
four-polynomial boundary factor. -/
theorem fourthFaberCombinationFactor_actual_coeff
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) :
    actualTaylorCoeff
      (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) k =
      actualTaylorCoeff
        (fun u : ℂ => u * thirdFaberCombinationFactor G α₁ α₂ α₃ u) k +
      α₄ * actualTaylorCoeff (fourthFaberFactor G) k := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hthree : AnalyticAt ℂ
      (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 := by
    unfold thirdFaberCombinationFactor
    fun_prop
  have hfour : AnalyticAt ℂ (fourthFaberFactor G) 0 := by
    unfold fourthFaberFactor
    fun_prop
  let f₁ : ℂ → ℂ := fun u =>
    u * thirdFaberCombinationFactor G α₁ α₂ α₃ u
  let f₂ : ℂ → ℂ := fun u => α₄ * fourthFaberFactor G u
  calc
    _ = actualTaylorCoeff f₁ k + actualTaylorCoeff f₂ k := by
      change actualTaylorCoeff (fun u => f₁ u + f₂ u) k = _
      exact actualTaylorCoeff_add_analytic f₁ f₂
        (analyticAt_id.mul hthree) (analyticAt_const.mul hfour) k
    _ = _ := by
      simp only [f₁, f₂, actualTaylorCoeff_const_mul_analytic]

/-- The four positive Fourier frequencies carry precisely the input
coordinates, in reverse Taylor order. -/
theorem fourthFaberCombinationFactor_actual_low_coefficients
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ : ℂ) :
    actualTaylorCoeff
        (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 0 = α₄ ∧
    actualTaylorCoeff
        (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 1 = α₃ ∧
    actualTaylorCoeff
        (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 2 = α₂ ∧
    actualTaylorCoeff
        (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 3 = α₁ := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hthree : AnalyticAt ℂ
      (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 := by
    unfold thirdFaberCombinationFactor
    fun_prop
  rcases thirdFaberCombinationFactor_actual_low_coefficients
    G hc α₁ α₂ α₃ with ⟨h30, h31, h32⟩
  rcases fourthFaberFactor_actual_low_coefficients G hc with
    ⟨h40, h41, h42, h43, h44⟩
  change actualTaylorCoeff (fourthFaberFactor G) 0 = 1 at h40
  change actualTaylorCoeff (fourthFaberFactor G) 1 = 0 at h41
  change actualTaylorCoeff (fourthFaberFactor G) 2 = 0 at h42
  change actualTaylorCoeff (fourthFaberFactor G) 3 = 0 at h43
  constructor
  · rw [fourthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ 0,
      actualTaylorCoeff_var_mul_zero, h40]
    ring
  constructor
  · rw [fourthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ 1,
      actualTaylorCoeff_var_mul_succ _ hthree 0, h30, h41]
    ring
  constructor
  · rw [fourthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ 2,
      actualTaylorCoeff_var_mul_succ _ hthree 1, h31, h42]
    ring
  · rw [fourthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ 3,
      actualTaylorCoeff_var_mul_succ _ hthree 2, h32, h43]
    ring

/-- The full four-polynomial Green area inequality for a regularized map.
The bound holds for every complex test vector; no one-row reduction is used. -/
theorem rescaleExterior_fourthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) :
    let A := fourthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄
    ‖actualTaylorCoeff A 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 8‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 := by
  let G := rescaleExterior s F
  let A := fourthFaberCombinationFactor G α₁ α₂ α₃ α₄
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h := fourthFaberCombination_actual_mode_energy_le
    F hc hs0 hs1 α₁ α₂ α₃ α₄
  change ‖actualTaylorCoeff A 5‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 8‖ ^ 2 ≤
    4 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      ‖actualTaylorCoeff A 3‖ ^ 2 at h
  rcases fourthFaberCombinationFactor_actual_low_coefficients
    G hcG α₁ α₂ α₃ α₄ with ⟨h0, h1, h2, h3⟩
  rw [h0, h1, h2, h3] at h
  convert h using 1; ring

end SpringerLean
