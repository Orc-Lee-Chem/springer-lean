import SpringerLean.Round89FaberBoundaryDerivative

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- A linear combination of the first three actual Faber polynomials. -/
noncomputable def thirdFaberCombinationPolynomial
    (G : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) : Polynomial ℂ :=
  Polynomial.C α₁ * firstFaberPolynomial G +
    Polynomial.C α₂ * secondFaberPolynomial G +
    Polynomial.C α₃ * thirdFaberPolynomial G

/-- All three leading Fourier frequencies are shifted to frequency three.
The remaining factor is analytic on the enlarged reciprocal disk. -/
noncomputable def thirdFaberCombinationFactor
    (G : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) (u : ℂ) : ℂ :=
  α₁ * u ^ 2 * exteriorPhi G u +
    α₂ * u * ((exteriorPhi G u) ^ 2 -
      2 * exteriorForwardCoeff G 1 * u ^ 2) +
    α₃ * ((exteriorPhi G u) ^ 3 -
      3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
      3 * exteriorForwardCoeff G 2 * u ^ 3)

theorem thirdFaberCombinationFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (α₁ α₂ α₃ : ℂ) :
    AnalyticOnNhd ℂ
      (thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hφ := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  unfold thirdFaberCombinationFactor
  fun_prop

theorem actualTaylorCoeff_add_analytic
    (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    actualTaylorCoeff (fun u => f u + g u) k =
      actualTaylorCoeff f k + actualTaylorCoeff g k := by
  calc
    _ = PowerSeries.coeff k (actualTaylorSeries (fun u => f u + g u)) := by
      rw [actualTaylorSeries_coeff]
    _ = PowerSeries.coeff k
        (actualTaylorSeries f + actualTaylorSeries g) := by
      rw [actualTaylorSeries_add f g hf hg]
    _ = _ := by simp

theorem actualTaylorCoeff_const_mul_analytic
    (c : ℂ) (f : ℂ → ℂ) (k : ℕ) :
    actualTaylorCoeff (fun u => c * f u) k =
      c * actualTaylorCoeff f k := by
  calc
    _ = PowerSeries.coeff k (actualTaylorSeries (fun u => c * f u)) := by
      rw [actualTaylorSeries_coeff]
    _ = PowerSeries.coeff k (PowerSeries.C c * actualTaylorSeries f) := by
      rw [actualTaylorSeries_const_mul]
    _ = _ := by simp

theorem actualTaylorCoeff_var_sq_mul_succ_succ
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    actualTaylorCoeff (fun u : ℂ => u ^ 2 * f u) (k + 2) =
      actualTaylorCoeff f k := by
  have hfun : (fun u : ℂ => u ^ 2 * f u) =
      (fun u : ℂ => u * (u * f u)) := by
    funext u
    ring
  rw [hfun]
  have huf : AnalyticAt ℂ (fun u : ℂ => u * f u) 0 := by
    fun_prop
  simpa only [show k + 2 = (k + 1) + 1 by omega] using
    (actualTaylorCoeff_var_mul_succ
      (fun u : ℂ => u * f u) huf (k + 1)).trans
      (actualTaylorCoeff_var_mul_succ f hf k)

theorem actualTaylorCoeff_var_mul_zero (f : ℂ → ℂ) :
    actualTaylorCoeff (fun u : ℂ => u * f u) 0 = 0 := by
  simp [actualTaylorCoeff]

theorem actualTaylorCoeff_var_sq_mul_zero (f : ℂ → ℂ) :
    actualTaylorCoeff (fun u : ℂ => u ^ 2 * f u) 0 = 0 := by
  simp [actualTaylorCoeff]

theorem actualTaylorCoeff_var_sq_mul_one
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    actualTaylorCoeff (fun u : ℂ => u ^ 2 * f u) 1 = 0 := by
  have hfun : (fun u : ℂ => u ^ 2 * f u) =
      (fun u : ℂ => u * (u * f u)) := by
    funext u
    ring
  rw [hfun, actualTaylorCoeff_var_mul_succ
    (fun u : ℂ => u * f u) (by fun_prop) 0]
  exact actualTaylorCoeff_var_mul_zero f

/-- Coefficient linearity for the actual three-term reciprocal factor.
The three summands are kept separate for later low-mode substitutions. -/
theorem thirdFaberCombinationFactor_actual_coeff
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (thirdFaberCombinationFactor G α₁ α₂ α₃) k =
      α₁ * actualTaylorCoeff
        (fun u : ℂ => u ^ 2 * exteriorPhi G u) k +
      α₂ * actualTaylorCoeff
        (fun u : ℂ => u *
          ((exteriorPhi G u) ^ 2 -
            2 * exteriorForwardCoeff G 1 * u ^ 2)) k +
      α₃ * actualTaylorCoeff
        (fun u : ℂ =>
          (exteriorPhi G u) ^ 3 -
          3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
          3 * exteriorForwardCoeff G 2 * u ^ 3) k := by
  let f₁ : ℂ → ℂ := fun u => u ^ 2 * exteriorPhi G u
  let f₂ : ℂ → ℂ := fun u => u *
    ((exteriorPhi G u) ^ 2 -
      2 * exteriorForwardCoeff G 1 * u ^ 2)
  let f₃ : ℂ → ℂ := fun u =>
    (exteriorPhi G u) ^ 3 -
      3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
      3 * exteriorForwardCoeff G 2 * u ^ 3
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have h₁ : AnalyticAt ℂ f₁ 0 := by
    dsimp [f₁]
    fun_prop
  have h₂ : AnalyticAt ℂ f₂ 0 := by
    dsimp [f₂]
    fun_prop
  have h₃ : AnalyticAt ℂ f₃ 0 := by
    dsimp [f₃]
    fun_prop
  have heq : thirdFaberCombinationFactor G α₁ α₂ α₃ =
      (fun u => (α₁ * f₁ u + α₂ * f₂ u) + α₃ * f₃ u) := by
    funext u
    dsimp [thirdFaberCombinationFactor, f₁, f₂, f₃]
    ring
  rw [heq]
  rw [actualTaylorCoeff_add_analytic _ _ (by fun_prop) (by fun_prop),
    actualTaylorCoeff_add_analytic _ _ (by fun_prop) (by fun_prop)]
  simp only [actualTaylorCoeff_const_mul_analytic]
  rfl

/-- The only positive Fourier modes of the combined boundary curve are
frequencies three, two, and one, with the original test coefficients. -/
theorem thirdFaberCombinationFactor_actual_low_coefficients
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ : ℂ) :
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 = α₃ ∧
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 1 = α₂ ∧
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 2 = α₁ := by
  rcases exteriorPhi_actual_low_coefficients G hc with ⟨hφ0, hφ1, hφ2, hφ3⟩
  rcases secondFaberFactor_actual_low_coefficients G hc with ⟨h20, h21, h22⟩
  rcases thirdFaberFactor_actual_low_coefficients G hc with
    ⟨h30, h31, h32, h33⟩
  have hA2 : AnalyticAt ℂ
      (fun u : ℂ => (exteriorPhi G u) ^ 2 -
        2 * exteriorForwardCoeff G 1 * u ^ 2) 0 := by
    have hφ := exteriorPhi_analyticAt G hc.2.2
    fun_prop
  constructor
  · rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 0]
    simp only [actualTaylorCoeff_var_sq_mul_zero,
      actualTaylorCoeff_var_mul_zero, h30]
    ring
  constructor
  · rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 1]
    rw [actualTaylorCoeff_var_sq_mul_one _
      (exteriorPhi_analyticAt G hc.2.2),
      actualTaylorCoeff_var_mul_succ _ hA2 0, h20, h31]
    ring
  · rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 2]
    have hsq := actualTaylorCoeff_var_sq_mul_succ_succ
      (exteriorPhi G) (exteriorPhi_analyticAt G hc.2.2) 0
    have hvar := actualTaylorCoeff_var_mul_succ
      (fun u : ℂ => (exteriorPhi G u) ^ 2 -
        2 * exteriorForwardCoeff G 1 * u ^ 2) hA2 1
    norm_num only at hsq hvar
    rw [hsq, hvar, hφ0, h21, h32]
    ring

/-- The first negative Fourier mode of the combined actual boundary curve
is the first column of the logarithmic Grunsky coefficient matrix. -/
theorem thirdFaberCombinationFactor_actual_mode_four
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ : ℂ) :
    let Q := schoberKernelQ3
      (exteriorForwardCoeff G 1) (exteriorForwardCoeff G 2)
      (exteriorForwardCoeff G 3) (exteriorForwardCoeff G 4)
      (exteriorForwardCoeff G 5)
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 4 =
      α₁ * schoberBiCoeff 1 1 Q +
      α₂ * (2 * schoberBiCoeff 2 1 Q) +
      α₃ * (3 * schoberBiCoeff 3 1 Q) := by
  dsimp only
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hA2 : AnalyticAt ℂ
      (fun u : ℂ => (exteriorPhi G u) ^ 2 -
        2 * exteriorForwardCoeff G 1 * u ^ 2) 0 := by
    fun_prop
  have hsq := actualTaylorCoeff_var_sq_mul_succ_succ
    (exteriorPhi G) hφ 2
  have hvar := actualTaylorCoeff_var_mul_succ
    (fun u : ℂ => (exteriorPhi G u) ^ 2 -
      2 * exteriorForwardCoeff G 1 * u ^ 2) hA2 3
  norm_num only at hsq hvar
  have hφ2 := actualTaylorCoeff_exteriorPhi_succ G hc 1
  norm_num only at hφ2
  rcases secondFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h23, h24, h25⟩
  rcases thirdFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h34, h35, h36⟩
  rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 4,
    hsq, hvar, hφ2, h23, h34,
    schoberKernelQ3_coeff_one_one]

theorem thirdFaberCombinationFactor_actual_mode_five
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ : ℂ) :
    let Q := schoberKernelQ3
      (exteriorForwardCoeff G 1) (exteriorForwardCoeff G 2)
      (exteriorForwardCoeff G 3) (exteriorForwardCoeff G 4)
      (exteriorForwardCoeff G 5)
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 5 =
      α₁ * schoberBiCoeff 1 2 Q +
      α₂ * (2 * schoberBiCoeff 2 2 Q) +
      α₃ * (3 * schoberBiCoeff 3 2 Q) := by
  dsimp only
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hA2 : AnalyticAt ℂ
      (fun u : ℂ => (exteriorPhi G u) ^ 2 -
        2 * exteriorForwardCoeff G 1 * u ^ 2) 0 := by
    fun_prop
  have hsq := actualTaylorCoeff_var_sq_mul_succ_succ
    (exteriorPhi G) hφ 3
  have hvar := actualTaylorCoeff_var_mul_succ
    (fun u : ℂ => (exteriorPhi G u) ^ 2 -
      2 * exteriorForwardCoeff G 1 * u ^ 2) hA2 4
  norm_num only at hsq hvar
  have hφ3 := actualTaylorCoeff_exteriorPhi_succ G hc 2
  norm_num only at hφ3
  rcases secondFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h23, h24, h25⟩
  rcases thirdFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h34, h35, h36⟩
  rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 5,
    hsq, hvar, hφ3, h24, h35,
    schoberKernelQ3_coeff_one_two]

theorem thirdFaberCombinationFactor_actual_mode_six
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ : ℂ) :
    let Q := schoberKernelQ3
      (exteriorForwardCoeff G 1) (exteriorForwardCoeff G 2)
      (exteriorForwardCoeff G 3) (exteriorForwardCoeff G 4)
      (exteriorForwardCoeff G 5)
    actualTaylorCoeff (thirdFaberCombinationFactor G α₁ α₂ α₃) 6 =
      α₁ * schoberBiCoeff 1 3 Q +
      α₂ * (2 * schoberBiCoeff 2 3 Q) +
      α₃ * (3 * schoberBiCoeff 3 3 Q) := by
  dsimp only
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hA2 : AnalyticAt ℂ
      (fun u : ℂ => (exteriorPhi G u) ^ 2 -
        2 * exteriorForwardCoeff G 1 * u ^ 2) 0 := by
    fun_prop
  have hsq := actualTaylorCoeff_var_sq_mul_succ_succ
    (exteriorPhi G) hφ 4
  have hvar := actualTaylorCoeff_var_mul_succ
    (fun u : ℂ => (exteriorPhi G u) ^ 2 -
      2 * exteriorForwardCoeff G 1 * u ^ 2) hA2 5
  norm_num only at hsq hvar
  have hφ4 := actualTaylorCoeff_exteriorPhi_succ G hc 3
  norm_num only at hφ4
  rcases secondFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h23, h24, h25⟩
  rcases thirdFaberFactor_actual_modes_eq_logKernel G hc with
    ⟨h34, h35, h36⟩
  rw [thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ 6,
    hsq, hvar, hφ4, h25, h36,
    schoberKernelQ3_coeff_one_three]

theorem thirdFaberCombinationPolynomial_boundary_factor
    (G : ℂ → ℂ) (α₁ α₂ α₃ : ℂ)
    (θ : AddCircle (2 * Real.pi)) :
    (thirdFaberCombinationPolynomial G α₁ α₂ α₃).eval
        (G (fourier 1 θ)) =
      fourier 3 θ *
        thirdFaberCombinationFactor G α₁ α₂ α₃ (fourier (-1) θ) := by
  let u : ℂ := fourier (-1) θ
  have h31 : fourier 3 θ * u ^ 2 = fourier 1 θ := by
    change fourier 3 θ * (fourier (-1) θ) ^ 2 = fourier 1 θ
    rw [fourier_neg_one_pow, ← fourier_add]
    norm_num
  have h32 : fourier 3 θ * u = fourier 2 θ := by
    change fourier 3 θ * fourier (-1) θ = fourier 2 θ
    rw [← fourier_add]
    norm_num
  simp only [thirdFaberCombinationPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    firstFaberPolynomial_boundary_factor,
    secondFaberPolynomial_boundary_factor,
    thirdFaberPolynomial_boundary_factor]
  change
    α₁ * (fourier 1 θ * exteriorPhi G u) +
      α₂ * (fourier 2 θ *
        ((exteriorPhi G u) ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2)) +
      α₃ * (fourier 3 θ *
        ((exteriorPhi G u) ^ 3 -
          3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
          3 * exteriorForwardCoeff G 2 * u ^ 3)) =
    fourier 3 θ *
      (α₁ * u ^ 2 * exteriorPhi G u +
        α₂ * u *
          ((exteriorPhi G u) ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2) +
        α₃ *
          ((exteriorPhi G u) ^ 3 -
            3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
            3 * exteriorForwardCoeff G 2 * u ^ 3))
  rw [← h31, ← h32]
  ring

/-- The real signed Green circulation of every actual three-term Faber
combination is nonnegative. No injectivity of the polynomial is assumed. -/
theorem thirdFaberCombination_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ : ℂ) :
    let A := thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 3 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (fourier 3 (t : AddCircle (2 * Real.pi)) *
            A (fourier (-1) (t : AddCircle (2 * Real.pi)))).im) θ := by
  dsimp only
  let G := rescaleExterior s F
  let P := thirdFaberCombinationPolynomial G α₁ α₂ α₃
  have h := faberPolynomial_actual_exterior_boundary_area_nonneg
    F hc hs0 hs1 P
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ((thirdFaberCombinationPolynomial (rescaleExterior s F) α₁ α₂ α₃).eval
      (rescaleExterior s F (greenPolar 1 θ))).re *
      deriv (fun t : ℝ =>
        ((thirdFaberCombinationPolynomial (rescaleExterior s F) α₁ α₂ α₃).eval
          (rescaleExterior s F (greenPolar 1 t))).im) θ at h
  simpa only [greenPolar_one_eq_fourier,
    thirdFaberCombinationPolynomial_boundary_factor] using h

/-- Finite derivative-read Taylor approximants to an arbitrary three-term
Faber combination converge in oriented area to the actual boundary curve. -/
theorem thirdFaberCombination_boundary_area_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ : ℂ) :
    let A := thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃
    let γn : ℕ → ℝ → ℂ := fun M θ =>
      fourier 3 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff A j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
    let γ : ℝ → ℂ := fun θ =>
      fourier 3 (θ : AddCircle (2 * Real.pi)) *
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
    _ hR (thirdFaberCombinationFactor_analyticOnNhd F hc hs0 α₁ α₂ α₃) 3

/-- The Fourier support of a degree-three leading mode multiplied by a
finite reciprocal Taylor polynomial. -/
noncomputable def thirdFaberFiniteSupport (M : ℕ) : Finset ℤ :=
  (Finset.range (M + 1)).image (fun j : ℕ => 3 - (j : ℤ))

theorem thirdFaberFiniteSupport_injective (M : ℕ) :
    Set.InjOn (fun j : ℕ => 3 - (j : ℤ))
      (Finset.range (M + 1) : Set ℕ) := by
  intro i hi j hj hij
  change 3 - (i : ℤ) = 3 - (j : ℤ) at hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact_mod_cast this

/-- This mode identity fixes the sign of every negative Laurent frequency. -/
theorem thirdFaber_fourier_mode (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier 3 θ * (fourier (-1) θ) ^ j =
      fourier (3 - (j : ℤ)) θ := by
  rw [fourier_neg_one_pow, ← fourier_add]
  congr 1

/-- A finite actual Taylor boundary curve is literally a finite Fourier
polynomial, so the existing orthogonality theorem applies unchanged. -/
theorem thirdFaberFiniteBoundary_eq_fourier
    (c : ℕ → ℂ) (M : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier 3 θ *
      (∑ j ∈ Finset.range (M + 1), c j * (fourier (-1) θ) ^ j) =
    finiteFourierPolynomial (2 * Real.pi)
      (thirdFaberFiniteSupport M)
      (fun m : ℤ => c (3 - m).toNat) θ := by
  classical
  rw [finiteFourierPolynomial, thirdFaberFiniteSupport,
    Finset.sum_image (thirdFaberFiniteSupport_injective M)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (3 - (3 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  calc
    fourier 3 θ * (c j * (fourier (-1) θ) ^ j) =
        c j * (fourier 3 θ * (fourier (-1) θ) ^ j) := by ring
    _ = c j * fourier (3 - (j : ℤ)) θ := by
      rw [thirdFaber_fourier_mode]

theorem thirdFaberFiniteSupport_signed_sum
    (c : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ thirdFaberFiniteSupport M,
      (m : ℝ) * ‖c (3 - m).toNat‖ ^ 2) =
      ∑ j ∈ Finset.range (M + 1),
        (3 - (j : ℝ)) * ‖c j‖ ^ 2 := by
  classical
  rw [thirdFaberFiniteSupport,
    Finset.sum_image (thirdFaberFiniteSupport_injective M)]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (3 - (3 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  push_cast
  ring

/-- Exact signed Green area of each finite Taylor boundary approximation. -/
theorem thirdFaberFiniteBoundary_oriented_area
    (c : ℕ → ℂ) (M : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 3 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
        deriv (fun t : ℝ =>
          (fourier 3 (t : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) =
      Real.pi * (∑ j ∈ Finset.range (M + 1),
        (3 - (j : ℝ)) * ‖c j‖ ^ 2) := by
  simpa only [thirdFaberFiniteBoundary_eq_fourier,
    thirdFaberFiniteSupport_signed_sum] using
    (finiteFourierPolynomial_oriented_boundary
      (thirdFaberFiniteSupport M)
      (fun m : ℤ => c (3 - m).toNat))

/-- Keeping the first three negative frequencies only can increase the
signed area, because every subsequent mode has a negative integer weight. -/
theorem thirdFaberFiniteSignedEnergy_le_firstThree
    (c : ℕ → ℂ) (M : ℕ) (hM : 6 ≤ M) :
    (∑ j ∈ Finset.range (M + 1),
      (3 - (j : ℝ)) * ‖c j‖ ^ 2) ≤
      3 * ‖c 0‖ ^ 2 + 2 * ‖c 1‖ ^ 2 + ‖c 2‖ ^ 2 -
        (‖c 4‖ ^ 2 + 2 * ‖c 5‖ ^ 2 + 3 * ‖c 6‖ ^ 2) := by
  let f : ℕ → ℝ := fun j => (3 - (j : ℝ)) * ‖c j‖ ^ 2
  have htail : (∑ j ∈ Finset.Ico 7 (M + 1), f j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hj7 : 7 ≤ j := (Finset.mem_Ico.mp hj).1
    dsimp [f]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hjr : (7 : ℝ) ≤ j := by exact_mod_cast hj7
      linarith
    · positivity
  have hsplit := Finset.sum_range_add_sum_Ico f (show 7 ≤ M + 1 by omega)
  have hhead : (∑ j ∈ Finset.range 7, f j) =
      3 * ‖c 0‖ ^ 2 + 2 * ‖c 1‖ ^ 2 + ‖c 2‖ ^ 2 -
        (‖c 4‖ ^ 2 + 2 * ‖c 5‖ ^ 2 + 3 * ‖c 6‖ ^ 2) := by
    simp [f, Finset.sum_range_succ]
    ring
  change (∑ j ∈ Finset.range (M + 1), f j) ≤ _
  linarith

/-- The genuine exterior map supplies a three-mode weighted energy bound
for every linear combination of the first three actual Faber polynomials.
The right side uses only the positive frequencies of the combined curve. -/
theorem thirdFaberCombination_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ : ℂ) :
    let A := thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃
    ‖actualTaylorCoeff A 4‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 5‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 6‖ ^ 2 ≤
      3 * ‖actualTaylorCoeff A 0‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 1‖ ^ 2 +
        ‖actualTaylorCoeff A 2‖ ^ 2 := by
  dsimp only
  let A := thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃
  let γ : ℝ → ℂ := fun θ =>
    fourier 3 (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hAdiff : Differentiable ℝ γ := by
    simpa only [γ, A] using
      (faberBoundaryFactor_differentiable
        (thirdFaberCombinationFactor (rescaleExterior s F) α₁ α₂ α₃)
        hR (thirdFaberCombinationFactor_analyticOnNhd
          F hc hs0 α₁ α₂ α₃) 3)
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
      thirdFaberCombination_boundary_area_nonneg F hc hs0 hs1 α₁ α₂ α₃
  have hlim : Filter.Tendsto
      (fun M => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (3 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2))
      Filter.atTop (nhds I) := by
    simpa only [thirdFaberFiniteBoundary_oriented_area, I, γ, A] using
      (thirdFaberCombination_boundary_area_tendsto
        F hc hs0 hs1 α₁ α₂ α₃)
  let B : ℝ :=
    3 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      ‖actualTaylorCoeff A 2‖ ^ 2 -
      (‖actualTaylorCoeff A 4‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 5‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 6‖ ^ 2)
  have hupper : I ≤ Real.pi * B :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨6, by
      intro M hM
      exact mul_le_mul_of_nonneg_left
        (thirdFaberFiniteSignedEnergy_le_firstThree
          (actualTaylorCoeff A) M hM) Real.pi_pos.le⟩)
  have hB : 0 ≤ B := by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  dsimp [B] at hB
  linarith

/-- The actual regularized map satisfies the finite unnormalized Grunsky
quadratic inequality for every complex three-component test vector. -/
theorem rescaleExterior_logKernel_three_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ : ℂ) :
    let G := rescaleExterior s F
    let Q := schoberKernelQ3
      (exteriorForwardCoeff G 1) (exteriorForwardCoeff G 2)
      (exteriorForwardCoeff G 3) (exteriorForwardCoeff G 4)
      (exteriorForwardCoeff G 5)
    ‖α₁ * schoberBiCoeff 1 1 Q +
        α₂ * (2 * schoberBiCoeff 2 1 Q) +
        α₃ * (3 * schoberBiCoeff 3 1 Q)‖ ^ 2 +
      2 * ‖α₁ * schoberBiCoeff 1 2 Q +
        α₂ * (2 * schoberBiCoeff 2 2 Q) +
        α₃ * (3 * schoberBiCoeff 3 2 Q)‖ ^ 2 +
      3 * ‖α₁ * schoberBiCoeff 1 3 Q +
        α₂ * (2 * schoberBiCoeff 2 3 Q) +
        α₃ * (3 * schoberBiCoeff 3 3 Q)‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 := by
  let G := rescaleExterior s F
  let A := thirdFaberCombinationFactor G α₁ α₂ α₃
  let Q := schoberKernelQ3
    (exteriorForwardCoeff G 1) (exteriorForwardCoeff G 2)
    (exteriorForwardCoeff G 3) (exteriorForwardCoeff G 4)
    (exteriorForwardCoeff G 5)
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h := thirdFaberCombination_actual_mode_energy_le
    F hc hs0 hs1 α₁ α₂ α₃
  change ‖actualTaylorCoeff A 4‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 5‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 6‖ ^ 2 ≤
    3 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      ‖actualTaylorCoeff A 2‖ ^ 2 at h
  rcases thirdFaberCombinationFactor_actual_low_coefficients
    G hcG α₁ α₂ α₃ with ⟨h0, h1, h2⟩
  have h4 := thirdFaberCombinationFactor_actual_mode_four
    G hcG α₁ α₂ α₃
  have h5 := thirdFaberCombinationFactor_actual_mode_five
    G hcG α₁ α₂ α₃
  have h6 := thirdFaberCombinationFactor_actual_mode_six
    G hcG α₁ α₂ α₃
  change actualTaylorCoeff A 4 =
      α₁ * schoberBiCoeff 1 1 Q +
      α₂ * (2 * schoberBiCoeff 2 1 Q) +
      α₃ * (3 * schoberBiCoeff 3 1 Q) at h4
  change actualTaylorCoeff A 5 =
      α₁ * schoberBiCoeff 1 2 Q +
      α₂ * (2 * schoberBiCoeff 2 2 Q) +
      α₃ * (3 * schoberBiCoeff 3 2 Q) at h5
  change actualTaylorCoeff A 6 =
      α₁ * schoberBiCoeff 1 3 Q +
      α₂ * (2 * schoberBiCoeff 2 3 Q) +
      α₃ * (3 * schoberBiCoeff 3 3 Q) at h6
  rw [h0, h1, h2, h4, h5, h6] at h
  calc
    _ ≤ 3 * ‖α₃‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + ‖α₁‖ ^ 2 := h
    _ = _ := by ring

/-- The finite Grunsky quadratic form written directly in the five actual
forward coefficients. This expression is continuous in those coefficients. -/
noncomputable def thirdFaberQuadraticEnergy
    (b₁ b₂ b₃ b₄ b₅ α₁ α₂ α₃ : ℂ) : ℝ :=
  ‖α₁ * b₁ + α₂ * (2 * b₂) + α₃ * (3 * b₃)‖ ^ 2 +
    2 * ‖α₁ * b₂ + α₂ * (2 * b₃ + b₁ ^ 2) +
      α₃ * (3 * (b₄ + b₁ * b₂))‖ ^ 2 +
    3 * ‖α₁ * b₃ + α₂ * (2 * (b₄ + b₁ * b₂)) +
      α₃ * (3 * b₅ + 3 * b₁ * b₃ + 3 * b₂ ^ 2 + b₁ ^ 3)‖ ^ 2

theorem rescaleExterior_faber_quadratic_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ : ℂ) :
    thirdFaberQuadraticEnergy
      (exteriorForwardCoeff (rescaleExterior s F) 1)
      (exteriorForwardCoeff (rescaleExterior s F) 2)
      (exteriorForwardCoeff (rescaleExterior s F) 3)
      (exteriorForwardCoeff (rescaleExterior s F) 4)
      (exteriorForwardCoeff (rescaleExterior s F) 5)
      α₁ α₂ α₃ ≤
        ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 := by
  have h := rescaleExterior_logKernel_three_mode_energy_le
    F hc hs0 hs1 α₁ α₂ α₃
  dsimp only at h
  simp only [schoberKernelQ3_coeff_one_one,
    schoberKernelQ3_coeff_two_one,
    schoberKernelQ3_coeff_three_one,
    schoberKernelQ3_coeff_one_two,
    schoberKernelQ3_coeff_two_two,
    schoberKernelQ3_coeff_three_two,
    schoberKernelQ3_coeff_one_three,
    schoberKernelQ3_coeff_two_three,
    schoberKernelQ3_coeff_three_three] at h
  convert h using 1 <;> simp [thirdFaberQuadraticEnergy,
    schoberQ22, schoberQ33] <;> ring

/-- The finite Faber area inequality has now been transferred from every
regularized exterior map to the same actual map in the paper's function
class. There is no boundary regularity or Grunsky assumption in the type. -/
theorem exterior_faber_quadratic_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ : ℂ) :
    thirdFaberQuadraticEnergy
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) α₁ α₂ α₃ ≤
        ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  let E : ℝ → ℝ := fun s =>
    thirdFaberQuadraticEnergy
      ((s : ℂ) ^ 2 * b₁)
      ((s : ℂ) ^ 3 * b₂)
      ((s : ℂ) ^ 4 * b₃)
      ((s : ℂ) ^ 5 * b₄)
      ((s : ℂ) ^ 6 * b₅) α₁ α₂ α₃
  have hcont : Continuous E := by
    dsimp only [E]
    unfold thirdFaberQuadraticEnergy
    fun_prop
  have hlim : Filter.Tendsto
      (fun n : ℕ => E (omittedScaleSeq n)) Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 + 3 * ‖α₃‖ ^ 2 := by
    have h := rescaleExterior_faber_quadratic_energy_le
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      α₁ α₂ α₃
    simp only [rescaleExterior_forwardCoeff F hc
      (omittedScaleSeq_pos n)] at h
    exact h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa only [E, one_pow, one_mul, Complex.ofReal_one] using h

end SpringerLean
