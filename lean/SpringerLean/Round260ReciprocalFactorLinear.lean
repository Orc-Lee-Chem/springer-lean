import SpringerLean.Round255ActualFaberNormalization

namespace SpringerLean
open PowerSeries

@[simp] theorem polynomialFormalReciprocalFactor_zero
    (φ : PowerSeries ℂ) (N : ℕ) :
    polynomialFormalReciprocalFactor φ 0 N = 0 := by
  simp [polynomialFormalReciprocalFactor]

theorem polynomialFormalReciprocalFactor_add
    (φ : PowerSeries ℂ) (P Q : Polynomial ℂ) (N : ℕ) :
    polynomialFormalReciprocalFactor φ (P + Q) N =
      polynomialFormalReciprocalFactor φ P N +
        polynomialFormalReciprocalFactor φ Q N := by
  simp [polynomialFormalReciprocalFactor, add_mul, Finset.sum_add_distrib]

theorem polynomialFormalReciprocalFactor_const_mul
    (φ : PowerSeries ℂ) (a : ℂ) (P : Polynomial ℂ) (N : ℕ) :
    polynomialFormalReciprocalFactor φ (Polynomial.C a * P) N =
      PowerSeries.C a * polynomialFormalReciprocalFactor φ P N := by
  simp [polynomialFormalReciprocalFactor, Polynomial.coeff_C_mul,
    map_mul, Finset.mul_sum, mul_assoc]

theorem polynomialFormalReciprocalFactor_sum
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ)
    (φ : PowerSeries ℂ) (N : ℕ) :
    polynomialFormalReciprocalFactor φ (∑ i ∈ s, P i) N =
      ∑ i ∈ s, polynomialFormalReciprocalFactor φ (P i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        polynomialFormalReciprocalFactor_add, ih]

/-- A change of common leading frequency is multiplication by a power
of the reciprocal variable. No coefficient reindexing is assumed. -/
theorem polynomialFormalReciprocalFactor_shift
    (φ : PowerSeries ℂ) (P : Polynomial ℂ) (m N : ℕ)
    (hP : P.natDegree ≤ m) (hmN : m ≤ N) :
    polynomialFormalReciprocalFactor φ P N =
      PowerSeries.X ^ (N - m) * polynomialFormalReciprocalFactor φ P m := by
  let h := HahnSeries.ofPowerSeries ℤ ℂ
  have hy : h PowerSeries.X ≠ 0 := by
    intro hz
    have hx : (PowerSeries.X : PowerSeries ℂ) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
        (by simpa [h] using hz)
    exact PowerSeries.X_ne_zero hx
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  change h (polynomialFormalReciprocalFactor φ P N) = _
  rw [polynomialFormalReciprocalFactor_map φ P N (hP.trans hmN) h hy,
    map_mul, map_pow, polynomialFormalReciprocalFactor_map φ P m hP h hy,
    ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmN]

end SpringerLean
