import SpringerLean.Round763ChebyshevZeroPrelude

namespace SpringerLean

/-- The explicit first-derivative cosine grid lies between consecutive
Chebyshev T zero locations. Together with Round763's exact root formulas,
this is the first derivative case of the interlacing step for Proposition 9.2. -/
theorem chebyshev_first_derivative_grid_interlaces (n k : ℕ)
    (hn : 2 ≤ n) (hk : k + 1 < n) :
    Real.cos (((k : ℝ) + 1 / 2) * Real.pi / n) ≥
        Real.cos (((k : ℝ) + 1) * Real.pi / n) ∧
      Real.cos (((k : ℝ) + 1) * Real.pi / n) ≥
        Real.cos (((k : ℝ) + 3 / 2) * Real.pi / n) := by
  have hk2 : k + 2 ≤ n := by omega
  have hk2r : (k : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hk2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have ha0 : 0 ≤ ((k : ℝ) + 1 / 2) * Real.pi / n := by positivity
  have hb0 : 0 ≤ ((k : ℝ) + 1) * Real.pi / n := by positivity
  have hcpi : ((k : ℝ) + 3 / 2) * Real.pi / n ≤ Real.pi := by
    apply (div_le_iff₀ hn0).mpr
    have hgap : 0 ≤ (n : ℝ) - ((k : ℝ) + 3 / 2) := by linarith
    nlinarith [mul_nonneg hgap hpi]
  have hab : ((k : ℝ) + 1 / 2) * Real.pi / n ≤
      ((k : ℝ) + 1) * Real.pi / n := by
    gcongr
    norm_num
  have hbc : ((k : ℝ) + 1) * Real.pi / n ≤
      ((k : ℝ) + 3 / 2) * Real.pi / n := by
    gcongr
    norm_num
  have hbpi : ((k : ℝ) + 1) * Real.pi / n ≤ Real.pi := hbc.trans hcpi
  exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi ha0 hbpi hab,
    Real.cos_le_cos_of_nonneg_of_le_pi hb0 hcpi hbc⟩

end SpringerLean

#print axioms SpringerLean.chebyshev_first_derivative_grid_interlaces
