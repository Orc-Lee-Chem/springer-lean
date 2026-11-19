import SpringerLean.Round1456ActualTwoSavingBudget

namespace SpringerLean

/-- The two recurrence steps and the fourth-degree pointwise cosine
minorant leave a deficit below `0.502/n` from the first target order. -/
theorem refinedCandidate_cos_ratio_scalar
    {N : ℝ} (hN : 1501 ≤ N) :
    1-(251/500:ℝ)/N ≤
      ((N+1)*(2*N+9))/(2*(N+2)*(N+4)) := by
  have hN0 : 0 < N := by linarith
  have hden : 0 < 2*(N+2)*(N+4) := by positivity
  have hprod : 0 ≤ N*(N-244) :=
    mul_nonneg hN0.le (by linarith)
  apply (le_div_iff₀ hden).2
  field_simp [ne_of_gt hN0]
  nlinarith [hprod]

end SpringerLean

#print axioms SpringerLean.refinedCandidate_cos_ratio_scalar
