import SpringerLean.Round1650ActualPhaseModulusGradientBound

namespace SpringerLean

/-- The weighted transfer with an arbitrary baseline coefficient C.
The C=1 instance controls the antiholomorphic derivative term. -/
theorem weighted_derivative_transfer_general
    {K Y q p derivNorm C : ℝ}
    (hK : 0 < K) (hY : 0 < Y)
    (hq : 0 ≤ q) (hqY : q ≤ Y) (hp : 0 ≤ p)
    (hweighted : K*Y*derivNorm ≤ C*K*Y+p) :
    q*derivNorm ≤ C*q+p/K := by
  have hmul := mul_le_mul_of_nonneg_right hweighted hq
  have hpq := mul_le_mul_of_nonneg_left hqY hp
  have hprod : (K*q*derivNorm)*Y ≤ (C*K*q+p)*Y := by
    nlinarith [hmul, hpq]
  have hmain : K*q*derivNorm ≤ C*K*q+p :=
    le_of_mul_le_mul_right hprod hY
  have hdiff : (q*derivNorm-C*q)*K ≤ p := by
    nlinarith [hmain]
  have hdiv := (le_div_iff₀ hK).mpr hdiff
  nlinarith [hdiv]

end SpringerLean

#print axioms SpringerLean.weighted_derivative_transfer_general
