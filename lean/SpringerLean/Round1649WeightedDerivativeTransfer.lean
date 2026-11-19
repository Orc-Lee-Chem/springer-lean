import SpringerLean.Round1648ActualPhaseQuotientBound

namespace SpringerLean

/-- A zero-safe scalar transfer: a weighted derivative bound with
weight Y gives a bound with any smaller phase quotient q. -/
theorem weighted_derivative_transfer
    {K Y q p derivNorm : ℝ}
    (hK : 0 < K) (hY : 0 < Y)
    (hq : 0 ≤ q) (hqY : q ≤ Y) (hp : 0 ≤ p)
    (hweighted : K*Y*derivNorm ≤ 2*K*Y+p) :
    q*derivNorm ≤ 2*q+p/K := by
  have hmul := mul_le_mul_of_nonneg_right hweighted hq
  have hpq := mul_le_mul_of_nonneg_left hqY hp
  have hprod : (K*q*derivNorm)*Y ≤ (2*K*q+p)*Y := by
    nlinarith [hmul, hpq]
  have hmain : K*q*derivNorm ≤ 2*K*q+p :=
    le_of_mul_le_mul_right hprod hY
  have hdiff : (q*derivNorm-2*q)*K ≤ p := by
    nlinarith [hmain]
  have hdiv := (le_div_iff₀ hK).mpr hdiff
  nlinarith [hdiv]

end SpringerLean

#print axioms SpringerLean.weighted_derivative_transfer
