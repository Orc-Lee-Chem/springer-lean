import SpringerLean.Round172SixFaberSecondMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- A product with two vanishing low inner coefficients has no quadratic
inner term. This is independent of the number of outer variables retained. -/
theorem schoberBiCoeff_two_mul_of_low_zero
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA0 : schoberInnerConstantZero A)
    (hA1 : ∀ n : ℕ, schoberBiCoeff 1 n A = 0)
    (hB0 : schoberInnerConstantZero B) (n : ℕ) :
    schoberBiCoeff 2 n (A * B) = 0 := by
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [schoberInnerConstantZero] at hA0 hB0
  simp only [schoberBiCoeff] at hA1
  simp [hA0, hA1, hB0]

/-- The logarithmic terms of degree at least three cannot contribute to an
inner quadratic coefficient when every correction row is constant-free. -/
theorem schoberBiCoeff_two_pow_eq_zero
    {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (k n : ℕ) (hk : 3 ≤ k) :
    schoberBiCoeff 2 n (A ^ k) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hA20 : schoberInnerConstantZero (A ^ 2) :=
    schoberInnerConstantZero_pow hA 2 (by omega)
  have hA21 (p : ℕ) : schoberBiCoeff 1 p (A ^ 2) = 0 :=
    by simpa only [pow_two] using
      schoberBiCoeff_one_mul_of_innerConstantZero hA hA p
  have hB0 : schoberInnerConstantZero (A ^ (m + 1)) :=
    schoberInnerConstantZero_pow hA (m + 1) (by omega)
  rw [show A ^ (3 + m) = A ^ 2 * A ^ (m + 1) by ring]
  exact schoberBiCoeff_two_mul_of_low_zero hA20 hA21 hB0 n

/-- At inner degree two, a product of constant-free bivariate series is
the outer Cauchy product of their inner-linear coefficient sequences. -/
theorem schoberBiCoeff_two_mul_of_innerConstantZero
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (hB : schoberInnerConstantZero B) (n : ℕ) :
    schoberBiCoeff 2 n (A * B) =
      ∑ i ∈ Finset.range (n + 1),
        schoberBiCoeff 1 i A * schoberBiCoeff 1 (n - i) B := by
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [schoberInnerConstantZero] at hA hB
  simp [hA, hB]

end SpringerLean
