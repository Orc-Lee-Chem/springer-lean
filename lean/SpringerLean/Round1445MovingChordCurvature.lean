import SpringerLean.Round1444MovingActiveProfile

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 300000

/-- The smooth power and the actual maximum-profile power agree
throughout the moving arc. -/
theorem refinedAffine_moving_arc_profile_eq
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.sqrt (3*d)) :
    refinedAffineRadius W (2*Real.cos θ)^n =
      refinedAffineSmoothPower W n (2-2*Real.cos θ) := by
  let b : ℝ := Real.sqrt (3*d)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hd : d ≤ 1/1501 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le]
  have hbshort : b ≤ 1/20 := movingArc_b_le_one_twentieth hd0 hd
  have hS := movingArc_cos_deficit_quadratic hbshort hθ0 hθ
  have hbSq : b^2=3*d := Real.sq_sqrt (by positivity)
  have hθsq : θ^2 ≤ b^2 := by
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (add_nonneg hθ0 hb0)]
  have hns : (n:ℝ)*(2-2*Real.cos θ) ≤ 3 := by
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hS.2 hn0
    nlinarith [mul_le_mul_of_nonneg_left hθsq hn0, hnd]
  have hS0 : 0 ≤ 2-2*Real.cos θ := by
    linarith [Real.cos_le_one θ]
  have hactive := refinedAffineRadius_moving_active n hn hW0 hW hS0 hns
  have hangle : 2*Real.cos θ=2-(2-2*Real.cos θ) := by ring
  conv_lhs => rw [hangle,hactive]
  rfl

/-- The same active identity holds at the arc mean, the point where
the moving secant is anchored. -/
theorem refinedAffine_moving_mean_profile_eq
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let b := Real.sqrt (3*d)
    let μ := 2*Real.sin b/b
    let mean := (1/b)*(∫ θ in (0:ℝ)..b, (2-2*Real.cos θ))
    refinedAffineRadius W μ^n = refinedAffineSmoothPower W n mean := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hd : d ≤ 1/1501 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le]
  have hmeanBounds := refinedArc_mean_bounds hd0 hd
  have hb : 0 < b := hmeanBounds.1
  have hμlo : 2-d ≤ 2*Real.sin b/b := hmeanBounds.2.2.2.1
  have hμhi : 2*Real.sin b/b ≤ 2 := hmeanBounds.2.2.2.2
  have hmean := movingArc_deficit_mean_eq hb
  have hs0 : 0 ≤ 2-2*Real.sin b/b := by linarith
  have hns : (n:ℝ)*(2-2*Real.sin b/b) ≤ 3 := by
    have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left (by linarith : 2-2*Real.sin b/b ≤ d) hn0
    nlinarith [hnd]
  have hactive := refinedAffineRadius_moving_active n hn hW0 hW hs0 hns
  change refinedAffineRadius W (2*Real.sin b/b)^n = _
  rw [hmean]
  have heq : 2*Real.sin b/b=2-(2-2*Real.sin b/b) := by ring
  conv_lhs => rw [heq,hactive]
  rfl

end SpringerLean

#print axioms SpringerLean.refinedAffine_moving_arc_profile_eq
#print axioms SpringerLean.refinedAffine_moving_mean_profile_eq
