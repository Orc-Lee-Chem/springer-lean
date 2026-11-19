import SpringerLean.Round113KernelFiveFifth

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Fifth Faber polynomial for the same centered exterior map, with the
constant Laurent mode cancelled. -/
noncomputable def fifthFaberPolynomial (F : ℂ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 5 -
    Polynomial.C (5 * exteriorForwardCoeff F 1) * Polynomial.X ^ 3 -
    Polynomial.C (5 * exteriorForwardCoeff F 2) * Polynomial.X ^ 2 +
    Polynomial.C (5 * ((exteriorForwardCoeff F 1) ^ 2 -
      exteriorForwardCoeff F 3)) * Polynomial.X +
    Polynomial.C (5 * (exteriorForwardCoeff F 1 *
      exteriorForwardCoeff F 2 - exteriorForwardCoeff F 4))

/-- Reciprocal-coordinate analytic factor of the fifth Faber polynomial. -/
noncomputable def fifthFaberFactor (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  exteriorPhi F u ^ 5 -
    5 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u ^ 3 -
    5 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u ^ 2 +
    5 * ((exteriorForwardCoeff F 1) ^ 2 -
      exteriorForwardCoeff F 3) * u ^ 4 * exteriorPhi F u +
    5 * (exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 -
      exteriorForwardCoeff F 4) * u ^ 5

/-- The fifth Faber polynomial and the reciprocal factor use exactly the
same actual `F` and its independently defined forward coefficients. -/
theorem fifthFaberPolynomial_reciprocal_factor
    (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ^ 5 * (fifthFaberPolynomial F).eval (F u⁻¹) =
      fifthFaberFactor F u := by
  simp only [fifthFaberPolynomial, fifthFaberFactor, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [exteriorF_reciprocal_phi F hu]
  field_simp [hu]

/-- The actual fifth Faber boundary curve has leading Fourier frequency
five and the analytic reciprocal factor above. -/
theorem fifthFaberPolynomial_boundary_factor
    (F : ℂ → ℂ) (θ : AddCircle (2 * Real.pi)) :
    (fifthFaberPolynomial F).eval (F (fourier 1 θ)) =
      fourier 5 θ * fifthFaberFactor F (fourier (-1) θ) := by
  simpa only [Nat.cast_ofNat] using
    reciprocal_factor_to_fourier_boundary F (fifthFaberPolynomial F) 5
      (fifthFaberFactor F)
      (fun {u : ℂ} hu => fifthFaberPolynomial_reciprocal_factor F hu) θ

/-- The fifth Faber factor is analytic past the unit circle after
regularization; no boundary regularity is added to the function class. -/
theorem rescaleExterior_fifthFaberFactor_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    AnalyticOnNhd ℂ
      (fifthFaberFactor (rescaleExterior s F))
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hφ := rescaleExterior_phi_analyticOnNhd F hc hs0 u hu
  change AnalyticAt ℂ (fun x : ℂ =>
    exteriorPhi (rescaleExterior s F) x ^ 5 -
      5 * exteriorForwardCoeff (rescaleExterior s F) 1 * x ^ 2 *
        exteriorPhi (rescaleExterior s F) x ^ 3 -
      5 * exteriorForwardCoeff (rescaleExterior s F) 2 * x ^ 3 *
        exteriorPhi (rescaleExterior s F) x ^ 2 +
      5 * ((exteriorForwardCoeff (rescaleExterior s F) 1) ^ 2 -
        exteriorForwardCoeff (rescaleExterior s F) 3) * x ^ 4 *
        exteriorPhi (rescaleExterior s F) x +
      5 * (exteriorForwardCoeff (rescaleExterior s F) 1 *
        exteriorForwardCoeff (rescaleExterior s F) 2 -
        exteriorForwardCoeff (rescaleExterior s F) 4) * x ^ 5) u
  fun_prop

/-- Fourier frequencies of a fifth Faber boundary factor after a Taylor
truncation. -/
noncomputable def fifthFaberFiniteSupport (M : ℕ) : Finset ℤ :=
  (Finset.range (M + 1)).image (fun j : ℕ => 5 - (j : ℤ))

theorem fifthFaberFiniteSupport_injective (M : ℕ) :
    Set.InjOn (fun j : ℕ => 5 - (j : ℤ))
      (Finset.range (M + 1) : Set ℕ) := by
  intro i hi j hj hij
  change 5 - (i : ℤ) = 5 - (j : ℤ) at hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact_mod_cast this

theorem fifthFaber_fourier_mode (j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier 5 θ * (fourier (-1) θ) ^ j =
      fourier (5 - (j : ℤ)) θ := by
  rw [fourier_neg_one_pow, ← fourier_add]
  congr 1

theorem fifthFaberFiniteBoundary_eq_fourier
    (c : ℕ → ℂ) (M : ℕ) (θ : AddCircle (2 * Real.pi)) :
    fourier 5 θ *
      (∑ j ∈ Finset.range (M + 1), c j * (fourier (-1) θ) ^ j) =
    finiteFourierPolynomial (2 * Real.pi)
      (fifthFaberFiniteSupport M)
      (fun m : ℤ => c (5 - m).toNat) θ := by
  classical
  rw [finiteFourierPolynomial, fifthFaberFiniteSupport,
    Finset.sum_image (fifthFaberFiniteSupport_injective M)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (5 - (5 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  calc
    fourier 5 θ * (c j * (fourier (-1) θ) ^ j) =
        c j * (fourier 5 θ * (fourier (-1) θ) ^ j) := by ring
    _ = c j * fourier (5 - (j : ℤ)) θ := by
      rw [fifthFaber_fourier_mode]

theorem fifthFaberFiniteSupport_signed_sum
    (c : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ fifthFaberFiniteSupport M,
      (m : ℝ) * ‖c (5 - m).toNat‖ ^ 2) =
      ∑ j ∈ Finset.range (M + 1),
        (5 - (j : ℝ)) * ‖c j‖ ^ 2 := by
  classical
  rw [fifthFaberFiniteSupport,
    Finset.sum_image (fifthFaberFiniteSupport_injective M)]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : (5 - (5 - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  push_cast
  ring

theorem fifthFaberFiniteBoundary_oriented_area
    (c : ℕ → ℂ) (M : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier 5 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
        deriv (fun t : ℝ =>
          (fourier 5 (t : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) =
      Real.pi * (∑ j ∈ Finset.range (M + 1),
        (5 - (j : ℝ)) * ‖c j‖ ^ 2) := by
  simpa only [fifthFaberFiniteBoundary_eq_fourier,
    fifthFaberFiniteSupport_signed_sum] using
    (finiteFourierPolynomial_oriented_boundary
      (fifthFaberFiniteSupport M)
      (fun m : ℤ => c (5 - m).toNat))

/-- Frequencies beyond the first five negative modes can only lower
the signed boundary area. -/
theorem fifthFaberFiniteSignedEnergy_le_firstFive
    (c : ℕ → ℂ) (M : ℕ) (hM : 10 ≤ M) :
    (∑ j ∈ Finset.range (M + 1),
      (5 - (j : ℝ)) * ‖c j‖ ^ 2) ≤
      5 * ‖c 0‖ ^ 2 + 4 * ‖c 1‖ ^ 2 +
        3 * ‖c 2‖ ^ 2 + 2 * ‖c 3‖ ^ 2 + ‖c 4‖ ^ 2 -
        (‖c 6‖ ^ 2 + 2 * ‖c 7‖ ^ 2 +
          3 * ‖c 8‖ ^ 2 + 4 * ‖c 9‖ ^ 2 +
          5 * ‖c 10‖ ^ 2) := by
  let f : ℕ → ℝ := fun j => (5 - (j : ℝ)) * ‖c j‖ ^ 2
  have htail : (∑ j ∈ Finset.Ico 11 (M + 1), f j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hj11 : 11 ≤ j := (Finset.mem_Ico.mp hj).1
    dsimp [f]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hjr : (11 : ℝ) ≤ j := by exact_mod_cast hj11
      linarith
    · positivity
  have hsplit := Finset.sum_range_add_sum_Ico f (show 11 ≤ M + 1 by omega)
  have hhead : (∑ j ∈ Finset.range 11, f j) =
      5 * ‖c 0‖ ^ 2 + 4 * ‖c 1‖ ^ 2 +
        3 * ‖c 2‖ ^ 2 + 2 * ‖c 3‖ ^ 2 + ‖c 4‖ ^ 2 -
        (‖c 6‖ ^ 2 + 2 * ‖c 7‖ ^ 2 +
          3 * ‖c 8‖ ^ 2 + 4 * ‖c 9‖ ^ 2 +
          5 * ‖c 10‖ ^ 2) := by
    simp [f, Finset.sum_range_succ]
    ring
  change (∑ j ∈ Finset.range (M + 1), f j) ≤ _
  linarith

/-- Formal Taylor factor of the same actual fifth Faber polynomial. The
analytic-series bridge will identify this with `fifthFaberFactor F`. -/
noncomputable def fifthFaberFormalFactor (F : ℂ → ℂ) : PowerSeries ℂ :=
  let φ := formalExteriorPhi (exteriorFormalForward F)
  φ ^ 5 -
    PowerSeries.C (5 * exteriorForwardCoeff F 1) *
      PowerSeries.X ^ 2 * φ ^ 3 -
    PowerSeries.C (5 * exteriorForwardCoeff F 2) *
      PowerSeries.X ^ 3 * φ ^ 2 +
    PowerSeries.C (5 * ((exteriorForwardCoeff F 1) ^ 2 -
      exteriorForwardCoeff F 3)) * PowerSeries.X ^ 4 * φ +
    PowerSeries.C (5 * (exteriorForwardCoeff F 1 *
      exteriorForwardCoeff F 2 - exteriorForwardCoeff F 4)) *
      PowerSeries.X ^ 5

/-- Exact finite expansion in the shifted forward series
`g=∑ b_(j+1) X^j`; it isolates the first five Faber cancellations. -/
theorem fifthFaberFormalFactor_expand (F : ℂ → ℂ) :
    let f := exteriorFormalForward F
    let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
    fifthFaberFormalFactor F =
      1 + PowerSeries.X ^ 2 *
          (5 * g - PowerSeries.C (5 * exteriorForwardCoeff F 1)) -
        PowerSeries.X ^ 3 * PowerSeries.C (5 * exteriorForwardCoeff F 2) +
        PowerSeries.X ^ 4 *
          (10 * g ^ 2 -
            3 * PowerSeries.C (5 * exteriorForwardCoeff F 1) * g +
            PowerSeries.C (5 * ((exteriorForwardCoeff F 1) ^ 2 -
              exteriorForwardCoeff F 3))) +
        PowerSeries.X ^ 5 *
          (-(2 * PowerSeries.C (5 * exteriorForwardCoeff F 2) * g) +
            PowerSeries.C (5 * (exteriorForwardCoeff F 1 *
              exteriorForwardCoeff F 2 - exteriorForwardCoeff F 4))) +
        PowerSeries.X ^ 6 *
          (10 * g ^ 3 -
            3 * PowerSeries.C (5 * exteriorForwardCoeff F 1) * g ^ 2 +
            PowerSeries.C (5 * ((exteriorForwardCoeff F 1) ^ 2 -
              exteriorForwardCoeff F 3)) * g) -
        PowerSeries.X ^ 7 *
          (PowerSeries.C (5 * exteriorForwardCoeff F 2) * g ^ 2) +
        PowerSeries.X ^ 8 *
          (5 * g ^ 4 -
            PowerSeries.C (5 * exteriorForwardCoeff F 1) * g ^ 3) +
        PowerSeries.X ^ 10 * g ^ 5 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : formalExteriorPhi f = 1 + PowerSeries.X ^ 2 * g := by
    rw [formalExteriorPhi, hf]
    ring
  dsimp only [fifthFaberFormalFactor]
  rw [hφ]
  dsimp only [g, f]
  ring

/-- The independent derivative-read Taylor series of the genuine fifth
Faber factor is its formal factor, for the same actual map. -/
theorem fifthFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries (fifthFaberFactor F) =
      fifthFaberFormalFactor F := by
  let φ := exteriorPhi F
  let Φ := formalExteriorPhi (exteriorFormalForward F)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  have hφ : AnalyticAt ℂ φ 0 := exteriorPhi_analyticAt F hc.2.2
  have hterm (c : ℂ) (n k : ℕ) :
      actualTaylorSeries (fun u : ℂ => c * u ^ n * φ u ^ k) =
        PowerSeries.C c * PowerSeries.X ^ n * Φ ^ k := by
    have heq : (fun u : ℂ => c * u ^ n * φ u ^ k) =
        (fun u : ℂ => c * (u ^ n * φ u ^ k)) := by
      funext u
      ring
    rw [heq, actualTaylorSeries_const_mul,
      actualTaylorSeries_mul _ _ (by fun_prop : AnalyticAt ℂ (fun u : ℂ => u ^ n) 0)
        (by fun_prop : AnalyticAt ℂ (fun u : ℂ => φ u ^ k) 0),
      actualTaylorSeries_monomial, actualTaylorSeries_pow _ hφ,
      exteriorPhi_actualTaylorSeries F hc]
    simp only [mul_assoc]
    dsimp only [Φ]
  change actualTaylorSeries (fun u : ℂ =>
    φ u ^ 5 - 5 * b₁ * u ^ 2 * φ u ^ 3 -
      5 * b₂ * u ^ 3 * φ u ^ 2 +
      5 * (b₁ ^ 2 - b₃) * u ^ 4 * φ u +
      5 * (b₁ * b₂ - b₄) * u ^ 5) = _
  have hm4 : actualTaylorSeries
      (fun u : ℂ => 5 * (b₁ ^ 2 - b₃) * u ^ 4 * φ u) =
      PowerSeries.C (5 * (b₁ ^ 2 - b₃)) *
        PowerSeries.X ^ 4 * Φ := by
    simpa only [pow_one] using hterm (5 * (b₁ ^ 2 - b₃)) 4 1
  rw [actualTaylorSeries_add _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_add _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_pow _ hφ,
    hterm (5 * b₁) 2 3,
    hterm (5 * b₂) 3 2,
    hm4]
  rw [actualTaylorSeries_const_mul, actualTaylorSeries_monomial,
    exteriorPhi_actualTaylorSeries F hc]
  dsimp [fifthFaberFormalFactor, Φ, b₁, b₂, b₃, b₄]

/-- The fifth Faber factor has exactly one leading positive Fourier
frequency and no intervening nonnegative modes. -/
theorem fifthFaberFactor_actual_low_coefficients
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fifthFaberFactor F) 0 = 1 ∧
    actualTaylorCoeff (fifthFaberFactor F) 1 = 0 ∧
    actualTaylorCoeff (fifthFaberFactor F) 2 = 0 ∧
    actualTaylorCoeff (fifthFaberFactor F) 3 = 0 ∧
    actualTaylorCoeff (fifthFaberFactor F) 4 = 0 ∧
    actualTaylorCoeff (fifthFaberFactor F) 5 = 0 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using
      exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = b₁ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using
      exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = b₃ := by
    simpa [g, f, b₃, PowerSeries.coeff_mk] using
      exteriorFormalForward_coeff F 3
  have hg3 : PowerSeries.coeff 3 g = b₄ := by
    simpa [g, f, b₄, PowerSeries.coeff_mk] using
      exteriorFormalForward_coeff F 4
  have hsq0 : PowerSeries.constantCoeff (g ^ 2) = b₁ ^ 2 := by
    simp [hg0']
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) = 2 * b₁ * b₂ := by
    rw [PowerSeries.coeff_one_pow]
    simp [hg0', hg1]
    ring
  have hnat (n : ℕ) :
      PowerSeries.constantCoeff (n : PowerSeries ℂ) = (n : ℂ) := by
    simp only [map_natCast]
  have htwo : PowerSeries.constantCoeff (2 : PowerSeries ℂ) = 2 :=
    hnat 2
  have hthree : PowerSeries.constantCoeff (3 : PowerSeries ℂ) = 3 :=
    hnat 3
  have hfive : PowerSeries.constantCoeff (5 : PowerSeries ℂ) = 5 :=
    hnat 5
  have hten : PowerSeries.constantCoeff (10 : PowerSeries ℂ) = 10 :=
    hnat 10
  have hcoeff3 : PowerSeries.coeff 1 (3 : PowerSeries ℂ) = 0 := by
    have hC : PowerSeries.C (3 : ℂ) = (3 : PowerSeries ℂ) := by
      exact (map_natCast (PowerSeries.C : ℂ →+* PowerSeries ℂ) 3)
    rw [← hC]
    exact PowerSeries.coeff_C_of_ne_zero (by decide : (1 : ℕ) ≠ 0)
  have hreplace (m : ℕ) :
      actualTaylorCoeff (fifthFaberFactor F) m =
        PowerSeries.coeff m (fifthFaberFormalFactor F) := by
    rw [← actualTaylorSeries_coeff,
      fifthFaberFactor_actualTaylorSeries F hc]
  constructor
  · rw [hreplace 0, fifthFaberFormalFactor_expand F]
    simp
  constructor
  · rw [hreplace 1, fifthFaberFormalFactor_expand F]
    simp [PowerSeries.coeff_X_pow_mul']
  constructor
  · rw [hreplace 2, fifthFaberFormalFactor_expand F]
    simp [PowerSeries.coeff_X_pow_mul', hg0']
    rw [exteriorFormalForward_coeff F 1, hfive]
    ring
  constructor
  · rw [hreplace 3, fifthFaberFormalFactor_expand F]
    simp [PowerSeries.coeff_X_pow_mul', hg1]
    rw [exteriorFormalForward_coeff F 2]
    norm_num
  constructor
  · rw [hreplace 4, fifthFaberFormalFactor_expand F]
    simp [PowerSeries.coeff_X_pow_mul', hg2, hg0', hsq0]
    rw [exteriorFormalForward_coeff F 1,
      exteriorFormalForward_coeff F 3, hten, hthree]
    ring
  · rw [hreplace 5, fifthFaberFormalFactor_expand F]
    simp [PowerSeries.coeff_X_pow_mul', hg3, hg1, hg0', hsq1]
    simp only [PowerSeries.coeff_one_pow, PowerSeries.coeff_one_mul,
      PowerSeries.coeff_C_mul, map_natCast]
    simp [exteriorFormalForward_coeff]
    rw [hthree, htwo, hcoeff3]
    ring

end SpringerLean
