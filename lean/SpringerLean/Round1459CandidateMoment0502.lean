import SpringerLean.Round1458RefinedCosRatio

namespace SpringerLean

/-- Sharpened actual comparison-circle lower moment for every weak
Catalan candidate order, with the `0.502/n` margin needed by the
two-end joint deficit budget. -/
theorem comparisonCircleMoment_candidate_0502_lower
    (k : ℕ) (hk : 751 ≤ k) :
    (1-(251/500:ℝ)/((2*k-1:ℕ):ℝ))*
      Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 ≤
      ((2*k-1:ℕ):ℝ)*(catalan (k-1) : ℝ) := by
  let n : ℕ := 2*k-1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hcos := halfCosMoment_succ_refined_lower n hn
  have hfactor : 0 ≤ (2:ℝ)^(n+1)/Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcos hfactor
  have hcircle := comparisonCircleMoment_eq_halfCosMoment n
  have hcircleNext := comparisonCircleMoment_eq_halfCosMoment (n+1)
  have hpow : ((2:ℝ)^(n+1+1)/Real.pi*
      halfCosMoment (n+1))/2 =
      (2:ℝ)^(n+1)/Real.pi*halfCosMoment (n+1) := by
    rw [pow_succ]
    ring
  have hratio :
      (1-(251/500:ℝ)/(n:ℝ))*
        Real.circleAverage
          (fun ζ : ℂ => |2*ζ.re|^n) 0 1 ≤
        Real.circleAverage
          (fun ζ : ℂ => |2*ζ.re|^(n+1)) 0 1 /2 := by
    rw [hcircle,hcircleNext]
    rw [hpow]
    nlinarith [hscaled]
  have hnk : n+1=2*k := by dsimp [n]; omega
  rw [hnk,comparisonCircleMoment_even_half_eq_scaledCatalan k
    (by omega : 1≤k)] at hratio
  simpa only [n] using hratio

end SpringerLean

#print axioms SpringerLean.comparisonCircleMoment_candidate_0502_lower
