import SpringerLean.Round166KernelSixLowInput

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

theorem schoberLowEq_add {n : ℕ}
    {A B C D : PowerSeries (PowerSeries ℂ)}
    (hAC : schoberLowEq n A C) (hBD : schoberLowEq n B D) :
    schoberLowEq n (A + B) (C + D) := by
  intro i j hi hj
  simp only [schoberBiCoeff, map_add]
  rw [← schoberBiCoeff, ← schoberBiCoeff,
    hAC i j hi hj]
  rw [← schoberBiCoeff, ← schoberBiCoeff,
    hBD i j hi hj]

theorem schoberLowEq_const_mul {n : ℕ}
    (c : ℂ) {A B : PowerSeries (PowerSeries ℂ)}
    (hAB : schoberLowEq n A B) :
    schoberLowEq n
      (PowerSeries.C (PowerSeries.C c) * A)
      (PowerSeries.C (PowerSeries.C c) * B) := by
  intro i j hi hj
  simp only [schoberBiCoeff, PowerSeries.coeff_C_mul]
  exact congrArg (fun z : ℂ => c * z) (hAB i j hi hj)

/-- All twenty-five old entries of the sixth finite log kernel equal
the already verified fifth kernel. This uses a general low-coefficient
congruence under Cauchy products, so no high-order term is silently
dropped from the logarithmic expansion. -/
theorem schoberKernelQ6_low_block_eq_Q5
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ)
    (i j : Fin 5) :
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) := by
  let T6 := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  let T5 := schoberKernelT5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  let R := schoberKernelOuterR6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : schoberLowEq 6 T6 T5 :=
    schoberKernelT6_low_eq_T5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hp (k : ℕ) : schoberLowEq 6 (T6 ^ k) (T5 ^ k) :=
    schoberLowEq_pow hT k
  have ht (k : ℕ) (c : ℂ) : schoberLowEq 6
      (PowerSeries.C (PowerSeries.C c) * T6 ^ k)
      (PowerSeries.C (PowerSeries.C c) * T5 ^ k) :=
    schoberLowEq_const_mul c (hp k)
  have hzero : schoberLowEq 6
      (PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T6 ^ 6) 0 := by
    intro p q hpq hqq
    have hTX : T6 = PowerSeries.X * R :=
      schoberKernelT6_eq_X_mul_outerR6
        b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
    unfold schoberBiCoeff
    rw [PowerSeries.coeff_C_mul, hTX, mul_pow]
    have hcoeff : PowerSeries.coeff q (PowerSeries.X ^ 6 * R ^ 6) = 0 := by
      simp [PowerSeries.coeff_X_pow_mul', Nat.not_le_of_gt hqq]
    rw [hcoeff]
    simp
  have hbase : schoberLowEq 6
      (T6 + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T6 ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T6 ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T6 ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T6 ^ 5)
      (T5 + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T5 ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T5 ^ 3 +
        PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T5 ^ 4 +
        PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T5 ^ 5) := by
    exact schoberLowEq_add
      (schoberLowEq_add
        (schoberLowEq_add
          (schoberLowEq_add hT (ht 2 ((2 : ℂ)⁻¹)))
          (ht 3 ((3 : ℂ)⁻¹)))
        (ht 4 ((4 : ℂ)⁻¹)))
      (ht 5 ((5 : ℂ)⁻¹))
  have htotal := schoberLowEq_add hbase hzero
  have h := htotal (i.val + 1) (j.val + 1)
    (by omega) (by omega)
  simpa only [schoberKernelQ6, schoberKernelQ5, T6, T5,
    add_zero] using h

end SpringerLean
