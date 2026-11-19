import SpringerLean.Round114FaberFivePrelude

namespace SpringerLean

/-- The actual polynomial used for the five-vector Faber area test. -/
noncomputable def fifthFaberCombinationPolynomial
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ : ℂ) : Polynomial ℂ :=
  fourthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ +
    Polynomial.C α₅ * fifthFaberPolynomial G

/-- All five Faber factors share leading Fourier frequency five. -/
noncomputable def fifthFaberCombinationFactor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ : ℂ) (u : ℂ) : ℂ :=
  u * fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u +
    α₅ * fifthFaberFactor G u

theorem fifthFaberCombinationFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    AnalyticOnNhd ℂ
      (fifthFaberCombinationFactor (rescaleExterior s F)
        α₁ α₂ α₃ α₄ α₅)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hfour := fourthFaberCombinationFactor_analyticOnNhd
    F hc hs0 α₁ α₂ α₃ α₄ u hu
  have hfive := rescaleExterior_fifthFaberFactor_analyticOnNhd
    F hc hs0 u hu
  change AnalyticAt ℂ
    (fourthFaberCombinationFactor (rescaleExterior s F)
      α₁ α₂ α₃ α₄) u at hfour
  change AnalyticAt ℂ
    (fifthFaberFactor (rescaleExterior s F)) u at hfive
  change AnalyticAt ℂ (fun x : ℂ =>
    x * fourthFaberCombinationFactor (rescaleExterior s F)
      α₁ α₂ α₃ α₄ x +
      α₅ * fifthFaberFactor (rescaleExterior s F) x) u
  exact (analyticAt_id.mul hfour).add (analyticAt_const.mul hfive)

theorem fifthFaberCombinationPolynomial_boundary_factor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ : ℂ)
    (θ : AddCircle (2 * Real.pi)) :
    (fifthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ α₅).eval
        (G (fourier 1 θ)) =
      fourier 5 θ *
        fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅
          (fourier (-1) θ) := by
  let u : ℂ := fourier (-1) θ
  have h54 : fourier 5 θ * u = fourier 4 θ := by
    change fourier 5 θ * fourier (-1) θ = fourier 4 θ
    rw [← fourier_add]
    norm_num
  simp only [fifthFaberCombinationPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    fourthFaberCombinationPolynomial_boundary_factor,
    fifthFaberPolynomial_boundary_factor]
  change fourier 4 θ *
      fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u +
      α₅ * (fourier 5 θ * fifthFaberFactor G u) =
    fourier 5 θ *
      (u * fourthFaberCombinationFactor G α₁ α₂ α₃ α₄ u +
        α₅ * fifthFaberFactor G u)
  rw [← h54]
  ring

/-- Nonnegative signed area for every five-vector Faber combination.
Only the original map `F` is assumed univalent; the polynomial image
itself is not assumed univalent. -/
theorem fifthFaberCombination_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    let A := fifthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 5 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (fourier 5 (t : AddCircle (2 * Real.pi)) *
            A (fourier (-1) (t : AddCircle (2 * Real.pi)))).im) θ := by
  dsimp only
  let G := rescaleExterior s F
  let P := fifthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ α₅
  have h := faberPolynomial_actual_exterior_boundary_area_nonneg
    F hc hs0 hs1 P
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ((fifthFaberCombinationPolynomial
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅).eval
      (rescaleExterior s F (greenPolar 1 θ))).re *
      deriv (fun t : ℝ =>
        ((fifthFaberCombinationPolynomial
          (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅).eval
          (rescaleExterior s F (greenPolar 1 t))).im) θ at h
  simpa only [greenPolar_one_eq_fourier,
    fifthFaberCombinationPolynomial_boundary_factor] using h

/-- Taylor truncations of the five-vector factor converge in the actual
oriented boundary area. -/
theorem fifthFaberCombination_boundary_area_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    let A := fifthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅
    let γn : ℕ → ℝ → ℂ := fun M θ =>
      fourier 5 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff A j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
    let γ : ℝ → ℂ := fun θ =>
      fourier 5 (θ : AddCircle (2 * Real.pi)) *
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
    _ hR (fifthFaberCombinationFactor_analyticOnNhd
      F hc hs0 α₁ α₂ α₃ α₄ α₅) 5

/-- Green area bounds the first five negative Fourier modes of every
five-vector actual Faber combination. This is the regularized all-vector
estimate before identifying its low modes and taking `s ↑ 1`. -/
theorem fifthFaberCombination_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    let A := fifthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅
    ‖actualTaylorCoeff A 6‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 10‖ ^ 2 ≤
      5 * ‖actualTaylorCoeff A 0‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 1‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 2‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 3‖ ^ 2 +
        ‖actualTaylorCoeff A 4‖ ^ 2 := by
  dsimp only
  let A := fifthFaberCombinationFactor
    (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅
  let γ : ℝ → ℂ := fun θ =>
    fourier 5 (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hAdiff : Differentiable ℝ γ := by
    simpa only [γ, A] using
      (faberBoundaryFactor_differentiable A hR
        (fifthFaberCombinationFactor_analyticOnNhd
          F hc hs0 α₁ α₂ α₃ α₄ α₅) 5)
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
      fifthFaberCombination_boundary_area_nonneg
        F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅
  have hlim : Filter.Tendsto
      (fun M => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (5 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2))
      Filter.atTop (nhds I) := by
    simpa only [fifthFaberFiniteBoundary_oriented_area, I, γ, A] using
      (fifthFaberCombination_boundary_area_tendsto
        F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅)
  let B : ℝ :=
    5 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 3‖ ^ 2 +
      ‖actualTaylorCoeff A 4‖ ^ 2 -
      (‖actualTaylorCoeff A 6‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 10‖ ^ 2)
  have hupper : I ≤ Real.pi * B :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨10, by
      intro M hM
      exact mul_le_mul_of_nonneg_left
        (fifthFaberFiniteSignedEnergy_le_firstFive
          (actualTaylorCoeff A) M hM) Real.pi_pos.le⟩)
  have hB : 0 ≤ B := by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  dsimp [B] at hB
  linarith

end SpringerLean
