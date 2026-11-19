import SpringerLean.Round140FaberSixPrelude
import SpringerLean.Round115FiveCombination

namespace SpringerLean

/-- Six actual Faber polynomials, tested with arbitrary complex weights. -/
noncomputable def sixthFaberCombinationPolynomial
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) : Polynomial ℂ :=
  fifthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ α₅ +
    Polynomial.C α₆ * sixthFaberPolynomial G

/-- Their common analytic factor has positive Fourier carrier `+6`. -/
noncomputable def sixthFaberCombinationFactor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (u : ℂ) : ℂ :=
  u * fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ u +
    α₆ * sixthFaberFactor G u

theorem rescaleExterior_sixthFaberFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ (sixthFaberFactor (rescaleExterior s F))
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hφ := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  change AnalyticAt ℂ (sixthFaberFactor (rescaleExterior s F)) u
  unfold sixthFaberFactor
  fun_prop

theorem sixthFaberCombinationFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    AnalyticOnNhd ℂ
      (sixthFaberCombinationFactor (rescaleExterior s F)
        α₁ α₂ α₃ α₄ α₅ α₆) (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hfive := fifthFaberCombinationFactor_analyticOnNhd
    F hc hs0 α₁ α₂ α₃ α₄ α₅ u hu
  have hsix := rescaleExterior_sixthFaberFactor_analyticOnNhd
    F hc hs0 u hu
  change AnalyticAt ℂ (fun x : ℂ =>
    x * fifthFaberCombinationFactor (rescaleExterior s F)
      α₁ α₂ α₃ α₄ α₅ x +
      α₆ * sixthFaberFactor (rescaleExterior s F) x) u
  exact (analyticAt_id.mul hfive).add (analyticAt_const.mul hsix)

/-- The same actual boundary curve now carries all six Faber rows. -/
theorem sixthFaberCombinationPolynomial_boundary_factor
    (G : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ)
    (θ : AddCircle (2 * Real.pi)) :
    (sixthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ α₅ α₆).eval
        (G (fourier 1 θ)) =
      fourier 6 θ *
        sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆
          (fourier (-1) θ) := by
  let u : ℂ := fourier (-1) θ
  have h65 : fourier 6 θ * u = fourier 5 θ := by
    change fourier 6 θ * fourier (-1) θ = fourier 5 θ
    rw [← fourier_add]
    norm_num
  simp only [sixthFaberCombinationPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    fifthFaberCombinationPolynomial_boundary_factor,
    sixthFaberPolynomial_boundary_factor]
  change fourier 5 θ *
      fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ u +
      α₆ * (fourier 6 θ * sixthFaberFactor G u) =
    fourier 6 θ *
      (u * fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ u +
        α₆ * sixthFaberFactor G u)
  rw [← h65]
  ring

/-- The signed boundary area of every six-row combination is nonnegative.
Only the original exterior map is required to be univalent. -/
theorem sixthFaberCombination_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    let A := sixthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 6 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (fourier 6 (t : AddCircle (2 * Real.pi)) *
            A (fourier (-1) (t : AddCircle (2 * Real.pi)))).im) θ := by
  dsimp only
  let G := rescaleExterior s F
  let P := sixthFaberCombinationPolynomial G α₁ α₂ α₃ α₄ α₅ α₆
  have h := faberPolynomial_actual_exterior_boundary_area_nonneg
    F hc hs0 hs1 P
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ((sixthFaberCombinationPolynomial
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆).eval
      (rescaleExterior s F (greenPolar 1 θ))).re *
      deriv (fun t : ℝ =>
        ((sixthFaberCombinationPolynomial
          (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆).eval
          (rescaleExterior s F (greenPolar 1 t))).im) θ at h
  simpa only [greenPolar_one_eq_fourier,
    sixthFaberCombinationPolynomial_boundary_factor] using h

end SpringerLean
