import SpringerLean.Round1329ChebyshevNormalizedCounts

namespace SpringerLean

/-- The j-step root brackets retain the original ordered grid. -/
theorem RolleGridChain.original_brackets
    {p : Polynomial ℝ} {n j : ℕ} {x₀ : ℕ → ℝ}
    (C : RolleGridChain p n j x₀) :
    ∀ r ≤ j, ∀ i < n - r,
      x₀ (i + r) ≤ C.grid r i ∧ C.grid r i ≤ x₀ i := by
  intro r
  induction r with
  | zero =>
    intro _ i _
    simp [C.initial]
  | succ r ih =>
    intro hr i hi
    have hstep := C.interlacing r (by omega) i hi
    have hleft := (ih (by omega) (i + 1) (by omega)).1
    have hright := (ih (by omega) i (by omega)).2
    constructor
    · convert hleft.trans hstep.1.le using 1 <;> congr 1 <;> omega
    · exact hstep.2.le.trans hright

/-- A scalar normalization used for finite empirical moments.  The
bounded mass B, as well as both unnormalized discrepancy signs, is
needed to retain j/n rather than j/(n-j). -/
theorem normalized_real_sum_discrepancy
    (n j : ℕ) (hj : j < n) (A B C : ℝ)
    (hB0 : 0 ≤ B) (hBC : B ≤ ((n : ℝ) - j) * C)
    (hBA : B ≤ A) (hAB : A ≤ B + (j : ℝ) * C) :
    |A / n - B / ((n : ℝ) - j)| ≤ (j : ℝ) * C / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < (n : ℝ) - j := by
    have hjr : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hu : A * ((n : ℝ) - j) - B * n ≤
      (j : ℝ) * C * ((n : ℝ) - j) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hd.le,
      mul_nonneg hB0 hj0]
  have hl : B * n - A * ((n : ℝ) - j) ≤
      (j : ℝ) * C * ((n : ℝ) - j) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hBA) hd.le,
      mul_nonneg (sub_nonneg.mpr hBC) hj0]
  have heq : A / n - B / ((n : ℝ) - j) =
      (A * ((n : ℝ) - j) - B * n) / ((n : ℝ) * ((n : ℝ) - j)) := by
    field_simp
  have htarget : (j : ℝ) * C / n =
      ((j : ℝ) * C * ((n : ℝ) - j)) / ((n : ℝ) * ((n : ℝ) - j)) := by
    field_simp
  rw [heq, htarget, abs_div, abs_of_pos (mul_pos hn hd)]
  apply (div_le_div_iff_of_pos_right (mul_pos hn hd)).2
  exact abs_le.mpr ⟨by linarith [hl], hu⟩

end SpringerLean

#print axioms SpringerLean.RolleGridChain.original_brackets
#print axioms SpringerLean.normalized_real_sum_discrepancy
