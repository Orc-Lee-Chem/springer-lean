import SpringerLean.Round256ActualPolynomialFactor

namespace SpringerLean
open PowerSeries

theorem formalFaberKernel_map_constantCoeff
    {A : Type*} [CommRing A] (f : PowerSeries A) :
    PowerSeries.map (PowerSeries.constantCoeff : PowerSeries A →+* A)
      (formalFaberKernel f) = 0 := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n => simp [PowerSeries.coeff_map]

theorem formalFaberLogKernel_map_constantCoeff
    {A : Type*} [CommRing A] [Algebra ℚ A] (f : PowerSeries A) :
    PowerSeries.map (PowerSeries.constantCoeff : PowerSeries A →+* A)
      (-PowerSeries.logOf (1 - formalFaberKernel f)) = 0 := by
  rw [map_neg, formal_logOf_map _ _ (by simp), map_sub, map_one,
    formalFaberKernel_map_constantCoeff, sub_zero]
  simp [PowerSeries.logOf_eq]

theorem exteriorFormalGrunskyKernel_inner_zero (F : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff 0
      (PowerSeries.coeff n (exteriorFormalGrunskyKernel F)) = 0 := by
  have h := congrArg (PowerSeries.coeff n)
    (formalFaberLogKernel_map_constantCoeff (exteriorFormalForward F))
  simpa [exteriorFormalGrunskyKernel,
    PowerSeries.coeff_zero_eq_constantCoeff] using h

/-- The actual analytic reciprocal factor of the general Faber polynomial. -/
noncomputable def exteriorGeneralFaberFactor (F : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  polynomialReciprocalFactor F (exteriorGeneralFaberPolynomial F n) n

theorem exteriorGeneralFaberFactor_reciprocal_eval
    (F : ℂ → ℂ) (n : ℕ) {u : ℂ} (hu : u ≠ 0) :
    u ^ n * (exteriorGeneralFaberPolynomial F n).eval (F u⁻¹) =
      exteriorGeneralFaberFactor F n u := by
  exact polynomialReciprocalFactor_eq_reciprocal_eval F _ n
    (generalFaberPolynomial_natDegree_le (exteriorFormalForward F) n) hu

theorem exteriorGeneralFaberFactor_analyticAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    AnalyticAt ℂ (exteriorGeneralFaberFactor F n) 0 :=
  polynomialReciprocalFactor_analyticAt F hc _ n

/-- Uniform identity between actual Taylor derivatives and the logarithmic
kernel. Both sides use the same original F, with no scaling parameter. -/
theorem exteriorGeneralFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    actualTaylorSeries (exteriorGeneralFaberFactor F (n + 1)) =
      1 + PowerSeries.C ((n + 1 : ℕ) : ℂ) * PowerSeries.X ^ (n + 1) *
        PowerSeries.coeff (n + 1) (exteriorFormalGrunskyKernel F) := by
  rw [exteriorGeneralFaberFactor,
    polynomialReciprocalFactor_actualTaylorSeries F hc,
    exteriorGeneralFaberFormalFactor_normalization]

/-- Every actual negative Faber mode equals its all-order Grunsky
coefficient, with the exact row multiplier. -/
theorem exteriorGeneralFaberFactor_actual_negative_mode
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n j : ℕ) :
    actualTaylorCoeff (exteriorGeneralFaberFactor F (n + 1))
        ((n + 1) + (j + 1)) =
      ((n + 1 : ℕ) : ℂ) * PowerSeries.coeff (j + 1)
        (PowerSeries.coeff (n + 1) (exteriorFormalGrunskyKernel F)) := by
  rw [← actualTaylorSeries_coeff,
    exteriorGeneralFaberFactor_actualTaylorSeries F hc n]
  simp only [map_add, mul_assoc, PowerSeries.coeff_C_mul]
  simp [PowerSeries.coeff_X_pow_mul']

/-- The leading actual Faber Fourier mode is one and all remaining
nonnegative modes vanish, for arbitrary order. -/
theorem exteriorGeneralFaberFactor_actual_low_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n k : ℕ)
    (hk : k ≤ n + 1) :
    actualTaylorCoeff (exteriorGeneralFaberFactor F (n + 1)) k =
      if k = 0 then 1 else 0 := by
  rw [← actualTaylorSeries_coeff,
    exteriorGeneralFaberFactor_actualTaylorSeries F hc n]
  by_cases heq : k = n + 1
  · subst k
    simp only [map_add, mul_assoc, PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X_pow_mul', exteriorFormalGrunskyKernel_inner_zero]
  · have hlt : k < n + 1 := by omega
    simp only [map_add, mul_assoc, PowerSeries.coeff_C_mul]
    simp [
      PowerSeries.coeff_X_pow_mul', Nat.not_le.mpr hlt,
      PowerSeries.coeff_one]

end SpringerLean
