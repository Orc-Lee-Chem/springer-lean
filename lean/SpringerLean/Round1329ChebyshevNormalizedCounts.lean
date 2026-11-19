import SpringerLean.Round772ChebyshevZeroDiscrepancy

namespace SpringerLean
open Polynomial

/-- An abstract normalization of the Rolle count discrepancy.  Both signs
are retained; this is the finite CDF estimate needed for moment convergence. -/
theorem normalized_count_discrepancy
    (n j A B : ℕ) (hj : j < n) (hB : B ≤ n - j)
    (hBA : B ≤ A) (hAB : A ≤ B + j) :
    |(A : ℝ) / n - (B : ℝ) / (n - j)| ≤ (j : ℝ) / n := by
  have hd : (0 : ℝ) < n - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnj : (n : ℝ) = (n - j : ℝ) + j := by ring
  have hBA' : (B : ℝ) ≤ A := by exact_mod_cast hBA
  have hAB' : (A : ℝ) ≤ B + j := by exact_mod_cast hAB
  have hB' : (B : ℝ) ≤ (n - j : ℝ) := by
    have hnat : (B : ℝ) ≤ ((n - j : ℕ) : ℝ) := by exact_mod_cast hB
    have heq : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by
      have h := Nat.sub_add_cancel hj.le
      have hh : ((n - j : ℕ) : ℝ) + j = n := by exact_mod_cast h
      linarith
    linarith
  have hmain1 : (A : ℝ) * (n - j : ℝ) - B * n ≤ j * (n - j : ℝ) := by
    rw [hnj]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (B : ℝ) by positivity)
      (show (0 : ℝ) ≤ (j : ℝ) by positivity)]
  have hmain2 : (B : ℝ) * n - A * (n - j : ℝ) ≤ j * (n - j : ℝ) := by
    rw [hnj]
    nlinarith [mul_nonneg (sub_nonneg.mpr hBA') (le_of_lt hd)]
  have heq : (A : ℝ) / n - (B : ℝ) / (n - j) =
      ((A : ℝ) * (n - j : ℝ) - B * n) / ((n : ℝ) * (n - j : ℝ)) := by
    field_simp
  have htarget : (j : ℝ) / n =
      ((j : ℝ) * (n - j : ℝ)) / ((n : ℝ) * (n - j : ℝ)) := by
    field_simp
  rw [heq, htarget]
  apply abs_le.mpr
  constructor
  · have hden := mul_pos hn hd
    have hlow : (-(j : ℝ) * (n - j : ℝ)) / ((n : ℝ) * (n - j : ℝ)) ≤
        ((A : ℝ) * (n - j : ℝ) - B * n) / ((n : ℝ) * (n - j : ℝ)) := by
      apply (div_le_div_iff₀ hden hden).2
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ j * (n - j : ℝ) +
          ((A : ℝ) * (n - j : ℝ) - B * n) by linarith [hmain2])
        (le_of_lt hden)]
    simpa only [neg_mul, neg_div] using hlow
  · have hden := mul_pos hn hd
    apply (div_le_div_iff₀ hden hden).2
    nlinarith [mul_nonneg
      (show (0 : ℝ) ≤ j * (n - j : ℝ) -
        ((A : ℝ) * (n - j : ℝ) - B * n) by linarith [hmain1])
      (le_of_lt hden)]

/-- The actual zero-count distributions of `T_n` and its `j`th derivative
differ by at most `j/n` at every threshold, with multiplicity counted. -/
theorem chebyshev_derivative_normalized_upper_count (n j : ℕ)
    (hj : j < n) (t : ℝ) :
    |(upperRealRootCount (Chebyshev.T ℝ (n : ℤ)) t : ℝ) / n -
      (upperRealRootCount ((Polynomial.derivative^[j])
        (Chebyshev.T ℝ (n : ℤ))) t : ℝ) / (n - j)| ≤ (j : ℝ) / n := by
  have hpair := chebyshev_derivative_zero_count_discrepancy n j hj t
  have hB : upperRealRootCount ((Polynomial.derivative^[j])
      (Chebyshev.T ℝ (n : ℤ))) t ≤ n - j := by
    rw [chebyshev_derivative_upperRootCount_eq_grid n j hj t]
    unfold upperGridCount
    calc
      (∑ k ∈ Finset.range (n - j),
          if t ≤ (chebyshevRolleChain n j hj.le).grid j k then 1 else 0)
          ≤ ∑ _k ∈ Finset.range (n - j), 1 := by
            apply Finset.sum_le_sum
            intro k hk
            split_ifs <;> omega
      _ = n - j := by simp
  exact normalized_count_discrepancy n j _ _ hj hB hpair.1 hpair.2

end SpringerLean

#print axioms SpringerLean.chebyshev_derivative_normalized_upper_count
