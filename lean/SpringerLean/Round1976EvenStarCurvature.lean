import SpringerLean.Round1891EvenStarScalarBridge

namespace SpringerLean

/-- The elementary curvature estimate used in the even-star argument.
With `y = exp (x / k) / 2^(1/k)`, the logarithmic term has second
derivative `y / (k^2 * (1+y)^2)`; the correction term has second
derivative `y^(2*k) / (4*k^2)`. This lemma compares their numerators
for the full paper range `0 ≤ y ≤ 1`, `k ≥ 1`. -/
theorem evenStar_log_kernel_curvature
    (k : ℕ) (hk : 1 ≤ k) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y ^ (2 * k) / 4 ≤ y / (1 + y) ^ 2 := by
  have hexp : 1 ≤ 2 * k := by omega
  have hpow : y ^ (2 * k) ≤ y := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * k = n + 1 :=
      ⟨2 * k - 1, by omega⟩
    rw [hn, pow_succ]
    have hunit : y ^ n ≤ 1 := pow_le_one₀ hy0 hy1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hunit hy0
  have hdenpos : 0 < (1 + y) ^ 2 := by positivity
  have hden : (1 + y) ^ 2 ≤ (4 : ℝ) := by nlinarith
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hdenpos).2
  calc
    y ^ (2 * k) * (1 + y) ^ 2 ≤ y * (1 + y) ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ ≤ y * 4 := mul_le_mul_of_nonneg_left hden hy0

end SpringerLean

#print axioms SpringerLean.evenStar_log_kernel_curvature
