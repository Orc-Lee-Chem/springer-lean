import SpringerLean.Round1524ActualClippedMomentNoSignPremise

namespace SpringerLean
set_option maxHeartbeats 320000

/-- At every real model value, clipping at a nonnegative cap reduces
the positive-part power. -/
theorem clippedTangentPower_le_positivePart_pow
    {M x : ℝ} (hM : 0 ≤ M) (m : ℕ) :
    clippedTangentPower M m x ≤ (max x 0)^m := by
  by_cases hx : x ≤ M
  · rw [clippedTangentPower_eq_positivePart_pow hx]
  · have hMx : M < x := lt_of_not_ge hx
    have hx0 : 0 ≤ x := hM.trans hMx.le
    rw [clippedTangentPower_eq_tangent hMx]
    simpa [powerTangent,max_eq_left hx0] using
      power_tangent_le hM hx0 m

/-- The model's positive power loses strictly wherever its value
exceeds the cap, for every exponent m>=2. -/
theorem clippedTangentPower_lt_positivePart_pow
    {M x : ℝ} (hM : 0 ≤ M) (hMx : M < x)
    {m : ℕ} (hm : 2 ≤ m) :
    clippedTangentPower M m x < (max x 0)^m := by
  have hx0 : 0 ≤ x := hM.trans hMx.le
  rw [clippedTangentPower_eq_tangent hMx]
  simpa [powerTangent,max_eq_left hx0] using
    power_tangent_lt hM hMx hm

end SpringerLean

#print axioms SpringerLean.clippedTangentPower_le_positivePart_pow
#print axioms SpringerLean.clippedTangentPower_lt_positivePart_pow
