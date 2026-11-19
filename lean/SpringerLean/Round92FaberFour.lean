import SpringerLean.Round91MatrixNormalization

namespace SpringerLean

/-- The fourth Faber polynomial in the centered exterior normalization.
The constant correction is `4*b₃-2*b₁²`, as fixed by cancellation of the
constant Laurent mode after the quadratic correction. -/
noncomputable def fourthFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 4 -
    Polynomial.C (4 * exteriorForwardCoeff F 1) * Polynomial.X ^ 2 -
    Polynomial.C (4 * exteriorForwardCoeff F 2) * Polynomial.X -
    Polynomial.C (4 * exteriorForwardCoeff F 3 -
      2 * (exteriorForwardCoeff F 1) ^ 2)

/-- Exact actual reciprocal-coordinate factorization. This checks the
fourth Faber correction against the same actual F and the established
forward-germ interface. -/
theorem fourthFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ^ 4 * (fourthFaberPolynomial F).eval (F u⁻¹) =
      (exteriorPhi F u) ^ 4 -
        4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
        4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
        (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4 := by
  simp only [fourthFaberPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

/-- The actual fourth Faber polynomial has a frequency-four boundary
factor, with the reciprocal correction analytic past the unit circle after
regularization. -/
theorem fourthFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (fourthFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 4 θ *
        ((exteriorPhi F (fourier (-1) θ)) ^ 4 -
          4 * exteriorForwardCoeff F 1 *
            (fourier (-1) θ) ^ 2 *
            (exteriorPhi F (fourier (-1) θ)) ^ 2 -
          4 * exteriorForwardCoeff F 2 *
            (fourier (-1) θ) ^ 3 *
            exteriorPhi F (fourier (-1) θ) -
          (4 * exteriorForwardCoeff F 3 -
            2 * (exteriorForwardCoeff F 1) ^ 2) *
            (fourier (-1) θ) ^ 4) := by
  simpa only [Nat.cast_ofNat] using
    reciprocal_factor_to_fourier_boundary F (fourthFaberPolynomial F) 4
      (fun u =>
        (exteriorPhi F u) ^ 4 -
          4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
          4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
          (4 * exteriorForwardCoeff F 3 -
            2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4)
      (fun {u : ℂ} hu => fourthFaberPolynomial_reciprocal_factor F hu) θ

theorem rescaleExterior_fourthFaberFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ
      (fun u : ℂ =>
        (exteriorPhi (rescaleExterior s F) u) ^ 4 -
          4 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2 *
            (exteriorPhi (rescaleExterior s F) u) ^ 2 -
          4 * exteriorForwardCoeff (rescaleExterior s F) 2 * u ^ 3 *
            exteriorPhi (rescaleExterior s F) u -
          (4 * exteriorForwardCoeff (rescaleExterior s F) 3 -
            2 * (exteriorForwardCoeff (rescaleExterior s F) 1) ^ 2) *
            u ^ 4)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hφ := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  fun_prop

/-- The fourth reciprocal Faber factor is read from the same actual
forward germ as all lower Faber factors. -/
theorem fourthFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries
      (fun u : ℂ => (exteriorPhi F u) ^ 4 -
        4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
        4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
        (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4) =
      (formalExteriorPhi (exteriorFormalForward F)) ^ 4 -
        PowerSeries.C (4 * exteriorForwardCoeff F 1) *
          PowerSeries.X ^ 2 *
            (formalExteriorPhi (exteriorFormalForward F)) ^ 2 -
        PowerSeries.C (4 * exteriorForwardCoeff F 2) *
          PowerSeries.X ^ 3 *
            formalExteriorPhi (exteriorFormalForward F) -
        PowerSeries.C (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * PowerSeries.X ^ 4 := by
  let φ := exteriorPhi F
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hφ : AnalyticAt ℂ φ 0 := exteriorPhi_analyticAt F hc.2.2
  have hm₂ : actualTaylorSeries (fun u : ℂ => 4 * b₁ * u ^ 2 * φ u ^ 2) =
      PowerSeries.C (4 * b₁) * PowerSeries.X ^ 2 *
        (formalExteriorPhi (exteriorFormalForward F)) ^ 2 := by
    have heq : (fun u : ℂ => 4 * b₁ * u ^ 2 * φ u ^ 2) =
        (fun u : ℂ => (4 * b₁) * (u ^ 2 * φ u ^ 2)) := by
      funext u; ring
    have hmul : actualTaylorSeries (fun u : ℂ => u ^ 2 * φ u ^ 2) =
        actualTaylorSeries (fun u : ℂ => u ^ 2) *
          actualTaylorSeries (fun u : ℂ => φ u ^ 2) := by
      exact actualTaylorSeries_mul _ _ (by fun_prop)
        (by fun_prop)
    rw [heq, actualTaylorSeries_const_mul, hmul,
      actualTaylorSeries_monomial, actualTaylorSeries_pow _ hφ,
      exteriorPhi_actualTaylorSeries F hc]
    simp only [mul_assoc]
  have hm₃ : actualTaylorSeries (fun u : ℂ => 4 * b₂ * u ^ 3 * φ u) =
      PowerSeries.C (4 * b₂) * PowerSeries.X ^ 3 *
        formalExteriorPhi (exteriorFormalForward F) := by
    have heq : (fun u : ℂ => 4 * b₂ * u ^ 3 * φ u) =
        (fun u : ℂ => (4 * b₂) * (u ^ 3 * φ u)) := by
      funext u; ring
    rw [heq, actualTaylorSeries_const_mul,
      actualTaylorSeries_mul _ _ (by fun_prop :
        AnalyticAt ℂ (fun u : ℂ => u ^ 3) 0) hφ,
      actualTaylorSeries_monomial, exteriorPhi_actualTaylorSeries F hc]
    simp only [mul_assoc]
  change actualTaylorSeries
      (fun u : ℂ => φ u ^ 4 - 4 * b₁ * u ^ 2 * φ u ^ 2 -
        4 * b₂ * u ^ 3 * φ u - (4 * b₃ - 2 * b₁ ^ 2) * u ^ 4) = _
  rw [actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_pow _ hφ, hm₂, hm₃,
    actualTaylorSeries_const_mul, actualTaylorSeries_monomial,
    exteriorPhi_actualTaylorSeries F hc]

/-- All four intervening nonnegative Fourier modes cancel in the actual
fourth Faber boundary factor. The constant term remains one. -/
theorem fourthFaberFactor_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi F u) ^ 4 -
        4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
        4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
        (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4
    actualTaylorCoeff A 0 = 1 ∧
    actualTaylorCoeff A 1 = 0 ∧
    actualTaylorCoeff A 2 = 0 ∧
    actualTaylorCoeff A 3 = 0 ∧
    actualTaylorCoeff A 4 = 0 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let A : ℂ → ℂ := fun u =>
    (exteriorPhi F u) ^ 4 - 4 * b₁ * u ^ 2 * (exteriorPhi F u) ^ 2 -
      4 * b₂ * u ^ 3 * exteriorPhi F u - (4 * b₃ - 2 * b₁ ^ 2) * u ^ 4
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = b₁ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = b₃ := by
    simpa [g, f, b₃, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hnat (n : ℕ) :
      PowerSeries.constantCoeff (n : PowerSeries ℂ) = (n : ℂ) := by
    simp only [map_natCast]
  have htwo : PowerSeries.constantCoeff (2 : PowerSeries ℂ) = 2 := by
    simpa using hnat 2
  have hfour : PowerSeries.constantCoeff (4 : PowerSeries ℂ) = 4 := by
    simpa using hnat 4
  have hsix : PowerSeries.constantCoeff (6 : PowerSeries ℂ) = 6 := by
    simpa using hnat 6
  let S : PowerSeries ℂ :=
    φ ^ 4 - PowerSeries.C (4 * b₁) * PowerSeries.X ^ 2 * φ ^ 2 -
      PowerSeries.C (4 * b₂) * PowerSeries.X ^ 3 * φ -
      PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2) * PowerSeries.X ^ 4
  have hA : S =
      1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
        PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
        PowerSeries.X ^ 4 *
          (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
            PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
        PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
        PowerSeries.X ^ 6 *
          (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
        PowerSeries.X ^ 8 * g ^ 4 := by
    dsimp [S]
    rw [hφ]
    ring
  have hreplace (m : ℕ) : actualTaylorCoeff A m = PowerSeries.coeff m S := by
    change actualTaylorCoeff
      (fun u : ℂ => (exteriorPhi F u) ^ 4 -
        4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
        4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
        (4 * exteriorForwardCoeff F 3 -
          2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4) m = _
    rw [← actualTaylorSeries_coeff,
      fourthFaberFactor_actualTaylorSeries F hc]
  dsimp only
  constructor
  · rw [hreplace 0, hA]
    simp
  constructor
  · rw [hreplace 1, hA]
    simp [PowerSeries.coeff_X_pow_mul']
  constructor
  · rw [hreplace 2, hA]
    simp [PowerSeries.coeff_X_pow_mul']
    rw [hg0', hfour]
    norm_num
  constructor
  · rw [hreplace 3, hA]
    simp [PowerSeries.coeff_X_pow_mul', hg1]
  · rw [hreplace 4, hA]
    simp [PowerSeries.coeff_X_pow_mul', hg2,
      PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hg0', hsix, htwo]
    ring

/-- Finite Fourier support for a boundary factor with leading frequency four. -/
noncomputable def fourthFaberFiniteSupport (M : ℕ) : Finset ℤ :=
  (Finset.range (M + 1)).image (fun j : ℕ => 4 - (j : ℤ))

theorem fourthFaberFiniteSupport_injective (M : ℕ) :
    Set.InjOn (fun j : ℕ => 4 - (j : ℤ))
      (Finset.range (M + 1) : Set ℕ) := by
  intro i hi j hj hij
  change 4 - (i : ℤ) = 4 - (j : ℤ) at hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact_mod_cast this

theorem fourthFaber_fourier_mode (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier 4 θ * (fourier (-1) θ) ^ j =
      fourier (4 - (j : ℤ)) θ := by
  rw [fourier_neg_one_pow, ← fourier_add]
  congr 1

theorem fourthFaberFiniteBoundary_eq_fourier
    (c : ℕ → ℂ) (M : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier 4 θ *
      (∑ j ∈ Finset.range (M + 1), c j * (fourier (-1) θ) ^ j) =
    finiteFourierPolynomial (2 * Real.pi)
      (fourthFaberFiniteSupport M)
      (fun m : ℤ => c (4 - m).toNat) θ := by
  classical
  rw [finiteFourierPolynomial, fourthFaberFiniteSupport,
    Finset.sum_image (fourthFaberFiniteSupport_injective M)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (4 - (4 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  calc
    fourier 4 θ * (c j * (fourier (-1) θ) ^ j) =
        c j * (fourier 4 θ * (fourier (-1) θ) ^ j) := by ring
    _ = c j * fourier (4 - (j : ℤ)) θ := by
      rw [fourthFaber_fourier_mode]

theorem fourthFaberFiniteSupport_signed_sum
    (c : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ fourthFaberFiniteSupport M,
      (m : ℝ) * ‖c (4 - m).toNat‖ ^ 2) =
      ∑ j ∈ Finset.range (M + 1),
        (4 - (j : ℝ)) * ‖c j‖ ^ 2 := by
  classical
  rw [fourthFaberFiniteSupport,
    Finset.sum_image (fourthFaberFiniteSupport_injective M)]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (4 - (4 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  push_cast
  ring

theorem fourthFaberFiniteBoundary_oriented_area
    (c : ℕ → ℂ) (M : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 4 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
        deriv (fun t : ℝ =>
          (fourier 4 (t : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) =
      Real.pi * (∑ j ∈ Finset.range (M + 1),
        (4 - (j : ℝ)) * ‖c j‖ ^ 2) := by
  simpa only [fourthFaberFiniteBoundary_eq_fourier,
    fourthFaberFiniteSupport_signed_sum] using
    (finiteFourierPolynomial_oriented_boundary
      (fourthFaberFiniteSupport M)
      (fun m : ℤ => c (4 - m).toNat))

/-- Every Fourier mode past the fourth negative mode only lowers signed area. -/
theorem fourthFaberFiniteSignedEnergy_le_firstFour
    (c : ℕ → ℂ) (M : ℕ) (hM : 8 ≤ M) :
    (∑ j ∈ Finset.range (M + 1),
      (4 - (j : ℝ)) * ‖c j‖ ^ 2) ≤
      4 * ‖c 0‖ ^ 2 + 3 * ‖c 1‖ ^ 2 +
        2 * ‖c 2‖ ^ 2 + ‖c 3‖ ^ 2 -
        (‖c 5‖ ^ 2 + 2 * ‖c 6‖ ^ 2 +
          3 * ‖c 7‖ ^ 2 + 4 * ‖c 8‖ ^ 2) := by
  let f : ℕ → ℝ := fun j => (4 - (j : ℝ)) * ‖c j‖ ^ 2
  have htail : (∑ j ∈ Finset.Ico 9 (M + 1), f j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hj9 : 9 ≤ j := (Finset.mem_Ico.mp hj).1
    dsimp [f]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hjr : (9 : ℝ) ≤ j := by exact_mod_cast hj9
      linarith
    · positivity
  have hsplit := Finset.sum_range_add_sum_Ico f (show 9 ≤ M + 1 by omega)
  have hhead : (∑ j ∈ Finset.range 9, f j) =
      4 * ‖c 0‖ ^ 2 + 3 * ‖c 1‖ ^ 2 +
        2 * ‖c 2‖ ^ 2 + ‖c 3‖ ^ 2 -
        (‖c 5‖ ^ 2 + 2 * ‖c 6‖ ^ 2 +
          3 * ‖c 7‖ ^ 2 + 4 * ‖c 8‖ ^ 2) := by
    simp [f, Finset.sum_range_succ]
    ring
  change (∑ j ∈ Finset.range (M + 1), f j) ≤ _
  linarith

/-- The genuine regularized exterior map makes the oriented area of the
fourth Faber image boundary nonnegative. -/
theorem fourthFaber_boundary_area_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let G := rescaleExterior s F
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi G u) ^ 4 -
        4 * exteriorForwardCoeff G 1 * u ^ 2 * (exteriorPhi G u) ^ 2 -
        4 * exteriorForwardCoeff G 2 * u ^ 3 * exteriorPhi G u -
        (4 * exteriorForwardCoeff G 3 -
          2 * (exteriorForwardCoeff G 1) ^ 2) * u ^ 4
    0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 4 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (fourier 4 (t : AddCircle (2 * Real.pi)) *
            A (fourier (-1) (t : AddCircle (2 * Real.pi)))).im) θ := by
  dsimp only
  let G := rescaleExterior s F
  let P := fourthFaberPolynomial G
  have h := faberPolynomial_actual_exterior_boundary_area_nonneg
    F hc hs0 hs1 P
  change 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ((fourthFaberPolynomial (rescaleExterior s F)).eval
      (rescaleExterior s F (greenPolar 1 θ))).re *
      deriv (fun t : ℝ =>
        ((fourthFaberPolynomial (rescaleExterior s F)).eval
          (rescaleExterior s F (greenPolar 1 t))).im) θ at h
  simpa only [greenPolar_one_eq_fourier,
    fourthFaberPolynomial_boundary_factor] using h

/-- Fourth Faber Taylor truncations converge in the actual oriented
boundary area integral. -/
theorem fourthFaber_boundary_area_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let G := rescaleExterior s F
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi G u) ^ 4 -
        4 * exteriorForwardCoeff G 1 * u ^ 2 * (exteriorPhi G u) ^ 2 -
        4 * exteriorForwardCoeff G 2 * u ^ 3 * exteriorPhi G u -
        (4 * exteriorForwardCoeff G 3 -
          2 * (exteriorForwardCoeff G 1) ^ 2) * u ^ 4
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
    _ hR (rescaleExterior_fourthFaberFactor_analyticOnNhd F hc hs0) 4

/-- The first four actual negative modes of the fourth Faber boundary
factor obey their exact weighted Green area bound. -/
theorem fourthFaber_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    let G := rescaleExterior s F
    let A : ℂ → ℂ := fun u =>
      (exteriorPhi G u) ^ 4 -
        4 * exteriorForwardCoeff G 1 * u ^ 2 * (exteriorPhi G u) ^ 2 -
        4 * exteriorForwardCoeff G 2 * u ^ 3 * exteriorPhi G u -
        (4 * exteriorForwardCoeff G 3 -
          2 * (exteriorForwardCoeff G 1) ^ 2) * u ^ 4
    ‖actualTaylorCoeff A 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 8‖ ^ 2 ≤ 4 := by
  dsimp only
  let G := rescaleExterior s F
  let A : ℂ → ℂ := fun u =>
    (exteriorPhi G u) ^ 4 -
      4 * exteriorForwardCoeff G 1 * u ^ 2 * (exteriorPhi G u) ^ 2 -
      4 * exteriorForwardCoeff G 2 * u ^ 3 * exteriorPhi G u -
      (4 * exteriorForwardCoeff G 3 -
        2 * (exteriorForwardCoeff G 1) ^ 2) * u ^ 4
  let γ : ℝ → ℂ := fun θ =>
    fourier 4 (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hAdiff : Differentiable ℝ γ := by
    simpa only [γ, A] using
      (faberBoundaryFactor_differentiable
        A hR (rescaleExterior_fourthFaberFactor_analyticOnNhd
          F hc hs0) 4)
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
    simpa only [γ, A, G] using
      fourthFaber_boundary_area_nonneg F hc hs0 hs1
  have hlim : Filter.Tendsto
      (fun M => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (4 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2))
      Filter.atTop (nhds I) := by
    simpa only [fourthFaberFiniteBoundary_oriented_area, I, γ, A, G] using
      (fourthFaber_boundary_area_tendsto F hc hs0 hs1)
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
  rcases fourthFaberFactor_actual_low_coefficients G
    (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1) with
    ⟨h0, h1, h2, h3, h4⟩
  change actualTaylorCoeff A 0 = 1 at h0
  change actualTaylorCoeff A 1 = 0 at h1
  change actualTaylorCoeff A 2 = 0 at h2
  change actualTaylorCoeff A 3 = 0 at h3
  dsimp [B] at hB
  rw [h0, h1, h2, h3] at hB
  norm_num at hB
  linarith

end SpringerLean
