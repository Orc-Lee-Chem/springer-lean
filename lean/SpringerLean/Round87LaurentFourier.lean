import SpringerLean.Round86BoundaryLimit

namespace SpringerLean

/-- A negative Fourier character raised from frequency minus one has exactly
the expected integer mode; this fixes the sign in the Laurent/Fourier bridge. -/
theorem fourier_neg_one_pow (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    (fourier (-1) θ) ^ j = fourier (-(j : ℤ)) θ := by
  induction j with
  | zero => simp [fourier_zero]
  | succ j ih =>
    rw [pow_succ, ih]
    have hi : -((j + 1 : ℕ) : ℤ) = -(j : ℤ) + (-1 : ℤ) := by omega
    rw [hi, fourier_add]

/-- Fourier support of the actual `M+1` Laurent partial boundary curve. -/
noncomputable def regularizedLaurentSupport (M : ℕ) : Finset ℤ :=
  insert 1 ((Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ)))

/-- The coefficient function on that support. Positive frequency one has
coefficient one; negative frequency minus j has coefficient `s^(j+1) b_j`. -/
noncomputable def regularizedLaurentModeCoeff
    (F : ℂ → ℂ) (s : ℝ) (m : ℤ) : ℂ :=
  if m = 1 then 1 else
    (s : ℂ) ^ (m.natAbs + 1) * exteriorForwardCoeff F m.natAbs

theorem regularizedLaurentModeCoeff_one
    (F : ℂ → ℂ) (s : ℝ) :
    regularizedLaurentModeCoeff F s 1 = 1 := by
  simp [regularizedLaurentModeCoeff]

theorem regularizedLaurentModeCoeff_neg_nat
    (F : ℂ → ℂ) (s : ℝ) (j : ℕ) :
    regularizedLaurentModeCoeff F s (-(j : ℤ)) =
      (s : ℂ) ^ (j + 1) * exteriorForwardCoeff F j := by
  have hj : -(j : ℤ) ≠ 1 := by omega
  simp [regularizedLaurentModeCoeff, hj]

theorem regularizedLaurentSupport_one_not_neg_range (M : ℕ) :
    (1 : ℤ) ∉ (Finset.range (M + 1)).image (fun j : ℕ => -(j : ℤ)) := by
  simp only [Finset.mem_image]
  rintro ⟨j, hj, h⟩
  omega

theorem regularizedLaurentSupport_neg_injective (M : ℕ) :
    Set.InjOn (fun j : ℕ => -(j : ℤ)) (Finset.range (M + 1) : Set ℕ) := by
  intro i hi j hj h
  have h' : (i : ℤ) = (j : ℤ) := neg_inj.mp h
  exact_mod_cast h'

/-- In the normalized finite signed energy, the only positive frequency is
one. The `-j` Laurent frequency contributes `-j |s^(j+1)b_j|²`; the zero
frequency contributes zero. -/
theorem regularizedLaurent_signed_sum_eq
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ) :
    (∑ m ∈ regularizedLaurentSupport M,
      (m : ℝ) * ‖regularizedLaurentModeCoeff F s m‖ ^ 2) =
    1 - ∑ j ∈ Finset.range (M + 1),
      (j : ℝ) * ‖(s : ℂ) ^ (j + 1) * exteriorForwardCoeff F j‖ ^ 2 := by
  classical
  rw [regularizedLaurentSupport,
    Finset.sum_insert (regularizedLaurentSupport_one_not_neg_range M)]
  rw [Finset.sum_image (regularizedLaurentSupport_neg_injective M)]
  simp_rw [regularizedLaurentModeCoeff_neg_nat]
  simp only [regularizedLaurentModeCoeff_one, norm_one, one_pow, mul_one,
    Int.cast_one, Int.cast_neg, Int.cast_natCast]
  simp_rw [neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The finite Taylor/Laurent partial curve is literally a finite Fourier
polynomial with its exact negative frequencies and scaling powers. -/
theorem rescaleExterior_boundary_partial_eq_finiteFourier
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier 1 θ + (s : ℂ) *
      (∑ j ∈ Finset.range (M + 1),
        exteriorForwardCoeff F j * ((s : ℂ) * fourier (-1) θ) ^ j) =
      finiteFourierPolynomial (2 * Real.pi)
        (regularizedLaurentSupport M)
        (regularizedLaurentModeCoeff F s) θ := by
  classical
  rw [finiteFourierPolynomial, regularizedLaurentSupport,
    Finset.sum_insert (regularizedLaurentSupport_one_not_neg_range M)]
  rw [Finset.sum_image (regularizedLaurentSupport_neg_injective M)]
  rw [regularizedLaurentModeCoeff_one]
  simp_rw [regularizedLaurentModeCoeff_neg_nat]
  rw [one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, fourier_neg_one_pow]
  ring

/-- Exact signed Fourier energy of each actual-coefficient Laurent partial
boundary curve. The right side includes all positive and negative integer
frequencies with their signs. -/
theorem rescaleExterior_boundary_partial_oriented_area
    (F : ℂ → ℂ) (s : ℝ) (M : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 1 (θ : AddCircle (2 * Real.pi)) +
        (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1)
              (θ : AddCircle (2 * Real.pi))) ^ j).re *
        deriv (fun t : ℝ =>
          (fourier 1 (t : AddCircle (2 * Real.pi)) +
            (s : ℂ) * ∑ j ∈ Finset.range (M + 1),
              exteriorForwardCoeff F j *
                ((s : ℂ) * fourier (-1)
                  (t : AddCircle (2 * Real.pi))) ^ j).im) θ) =
      Real.pi * ∑ m ∈ regularizedLaurentSupport M,
        (m : ℝ) * ‖regularizedLaurentModeCoeff F s m‖ ^ 2 := by
  simpa only [rescaleExterior_boundary_partial_eq_finiteFourier] using
    finiteFourierPolynomial_oriented_boundary
      (regularizedLaurentSupport M) (regularizedLaurentModeCoeff F s)

/-- The signed finite Fourier energies built from the actual original
coefficients converge to the true regularized boundary Green integral. -/
theorem rescaleExterior_boundary_signed_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Filter.Tendsto
      (fun M : ℕ => Real.pi * ∑ m ∈ regularizedLaurentSupport M,
        (m : ℝ) * ‖regularizedLaurentModeCoeff F s m‖ ^ 2)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (rescaleExterior s F
          (fourier 1 (θ : AddCircle (2 * Real.pi)))).re *
          deriv (fun t : ℝ =>
            (rescaleExterior s F
              (fourier 1 (t : AddCircle (2 * Real.pi)))).im) θ)) := by
  simpa only [rescaleExterior_boundary_partial_oriented_area] using
    rescaleExterior_boundary_oriented_integral_tendsto F hc hs0 hs1

/-- Explicit signed boundary-energy limit for the genuine regularized map:
the positive identity mode contributes one and every inverse-power mode
subtracts its degree-weighted squared coefficient. -/
theorem rescaleExterior_boundary_forward_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Filter.Tendsto
      (fun M : ℕ => Real.pi *
        (1 - ∑ j ∈ Finset.range (M + 1),
          (j : ℝ) * ‖(s : ℂ) ^ (j + 1) *
            exteriorForwardCoeff F j‖ ^ 2))
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (rescaleExterior s F
          (fourier 1 (θ : AddCircle (2 * Real.pi)))).re *
          deriv (fun t : ℝ =>
            (rescaleExterior s F
              (fourier 1 (t : AddCircle (2 * Real.pi)))).im) θ)) := by
  simpa only [regularizedLaurent_signed_sum_eq] using
    rescaleExterior_boundary_signed_energy_tendsto F hc hs0 hs1

/-- The standard Fourier circle and the polar circle used in the Green
argument are the same parameterized curve, with the same orientation. -/
@[simp] theorem greenPolar_one_eq_fourier (θ : ℝ) :
    greenPolar 1 θ = fourier 1 (θ : AddCircle (2 * Real.pi)) := by
  rw [greenPolar, fourier_coe_apply]
  simp only [Int.cast_one, Complex.ofReal_one, one_mul]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hpi]

/-- The true regularized boundary circulation for the identity polynomial
is the ordinary area of the actual omitted set, with the same unnormalized
Lebesgue area measure as Round81. -/
theorem rescaleExterior_boundary_oriented_eq_omitted_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (rescaleExterior s F
        (fourier 1 (θ : AddCircle (2 * Real.pi)))).re *
        deriv (fun t : ℝ =>
          (rescaleExterior s F
            (fourier 1 (t : AddCircle (2 * Real.pi)))).im) θ) =
      ∫ w in exteriorOmitted (rescaleExterior s F),
        (1 : ℝ) := by
  simpa only [Polynomial.eval_X, Polynomial.derivative_X,
    Polynomial.eval_one, norm_one, one_pow, greenPolar_one_eq_fourier] using
    faberPolynomial_actual_exterior_boundary_eq_omitted
      F hc hs0 hs1 (Polynomial.X : Polynomial ℂ)

/-- The actual regularized omitted area is the limit of the finite signed
Fourier energies of the original map's coefficients. -/
theorem rescaleExterior_omitted_area_eq_forward_energy_limit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Filter.Tendsto
      (fun M : ℕ => Real.pi *
        (1 - ∑ j ∈ Finset.range (M + 1),
          (j : ℝ) * ‖(s : ℂ) ^ (j + 1) *
            exteriorForwardCoeff F j‖ ^ 2))
      Filter.atTop
      (nhds (∫ w in exteriorOmitted (rescaleExterior s F),
        (1 : ℝ))) := by
  rw [← rescaleExterior_boundary_oriented_eq_omitted_area F hc hs0 hs1]
  exact rescaleExterior_boundary_forward_energy_tendsto F hc hs0 hs1

end SpringerLean
