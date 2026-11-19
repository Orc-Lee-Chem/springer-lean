import SpringerLean.Round175SixFaberKernelSecond

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The cubic inner coefficient of a product of constant-free bivariate
series has exactly the two middle Cauchy contributions. -/
theorem schoberBiCoeff_three_mul_of_innerConstantZero
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (hB : schoberInnerConstantZero B) (n : ℕ) :
    schoberBiCoeff 3 n (A * B) =
      ∑ i ∈ Finset.range (n + 1),
        (schoberBiCoeff 1 i A * schoberBiCoeff 2 (n - i) B +
          schoberBiCoeff 2 i A * schoberBiCoeff 1 (n - i) B) := by
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

/-- Powers of inner degree at least four cannot contribute to the cubic
inner coefficient of a logarithmic kernel. -/
theorem schoberBiCoeff_three_pow_eq_zero
    {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (k n : ℕ) (hk : 4 ≤ k) :
    schoberBiCoeff 3 n (A ^ k) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hA20 : schoberInnerConstantZero (A ^ 2) :=
    schoberInnerConstantZero_pow hA 2 (by omega)
  have hB0 : schoberInnerConstantZero (A ^ (m + 2)) :=
    schoberInnerConstantZero_pow hA (m + 2) (by omega)
  have hA21 (p : ℕ) : schoberBiCoeff 1 p (A ^ 2) = 0 :=
    schoberBiCoeff_one_pow_eq_zero hA 2 p (by omega)
  have hB1 (p : ℕ) : schoberBiCoeff 1 p (A ^ (m + 2)) = 0 :=
    schoberBiCoeff_one_pow_eq_zero hA (m + 2) p (by omega)
  rw [show A ^ (4 + m) = A ^ 2 * A ^ (m + 2) by ring,
    schoberBiCoeff_three_mul_of_innerConstantZero hA20 hB0]
  simp [hA21, hB1]

end SpringerLean
