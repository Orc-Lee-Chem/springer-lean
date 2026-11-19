import SpringerLean.Round1460Platform0018Scalar

namespace SpringerLean

/-- The platform contribution divided by the actual comparison-circle
moment is below `0.018/n`. -/
theorem refinedAffine_platform_normalized_0018
    (k : ℕ) (hk : 751 ≤ k) :
    let n : ℕ := 2*k-1
    let I : ℝ := Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1
    2*(n:ℝ)*(19/10:ℝ)^n/I < 18/1000 := by
  dsimp
  let n : ℕ := 2*k-1
  let N : ℝ := n
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0<n)
  have hIlo : (2:ℝ)^n/(2*N) ≤ I := by
    simpa only [n,N,I] using
      comparisonCircleMoment_odd_platform_lower k hk
  have hIpos : 0 < I := lt_of_lt_of_le (by positivity) hIlo
  have hfactor : 0 ≤ 4*N^2*(19/20:ℝ)^n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hIlo hfactor
  have hpow : (19/10:ℝ)^n=(2:ℝ)^n*(19/20:ℝ)^n := by
    rw [show (19/10:ℝ)=2*(19/20:ℝ) by norm_num,mul_pow]
  have heq : 4*N^2*(19/20:ℝ)^n*((2:ℝ)^n/(2*N)) =
      2*N*(19/10:ℝ)^n := by
    rw [hpow]
    field_simp [ne_of_gt hN]
    ring
  have hquot : 2*N*(19/10:ℝ)^n/I ≤
      4*N^2*(19/20:ℝ)^n := by
    apply (div_le_iff₀ hIpos).2
    nlinarith [hmul,heq]
  have hscalar := refinedAffine_platform_scalar_0018 n hn
  change 2*N*(19/10:ℝ)^n/I < 18/1000
  exact hquot.trans_lt hscalar

end SpringerLean

#print axioms SpringerLean.refinedAffine_platform_normalized_0018
