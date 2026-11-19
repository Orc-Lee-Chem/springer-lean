import SpringerLean.Round1443MovingQuantitativeJensen

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

/-- On a moving arc with deficit at most `3/n`, the affine profile is
strictly above its platform. This connects the smooth curvature
calculation to the actual refined projection test. -/
theorem refinedAffineRadius_moving_active
    (n : ℕ) (hn : 1501 ≤ n) {W s : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hs0 : 0 ≤ s) (hns : (n:ℝ)*s ≤ 3) :
    refinedAffineRadius W (2-s) =
      2*refinedAffineU W-refinedAffineV W*s := by
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : s ≤ 3/1501 := by
    have hmul := mul_le_mul_of_nonneg_right hnlarge hs0
    nlinarith [hmul]
  have hbase : (19/10:ℝ) ≤
      2*refinedAffineU W-refinedAffineV W*s := by
    dsimp [refinedAffineU, refinedAffineV]
    nlinarith [mul_nonneg hW0 hs0, sq_nonneg W]
  unfold refinedAffineRadius
  rw [max_eq_right]
  · dsimp [refinedAffineU,refinedAffineV]
    ring
  · convert hbase using 1 <;> (dsimp [refinedAffineU,refinedAffineV]; ring)

theorem movingArc_deficit_mean_eq
    {b : ℝ} (hb : 0 < b) :
    (1/b)*(∫ θ in (0:ℝ)..b, (2-2*Real.cos θ)) =
      2-2*Real.sin b/b := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((Real.continuous_cos.const_mul 2).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_cos]
  field_simp [ne_of_gt hb]

end SpringerLean

#print axioms SpringerLean.refinedAffineRadius_moving_active
#print axioms SpringerLean.movingArc_deficit_mean_eq
