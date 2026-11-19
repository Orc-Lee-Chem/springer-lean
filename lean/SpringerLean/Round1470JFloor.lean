import SpringerLean.Round1469LogCubeCore

namespace SpringerLean

/-- The one-sided J expression has a uniform floor. Together with
the actual joint `0.52` bound, this leaves each side below `0.58`. -/
theorem refinedAffineJ_floor
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht : t < 1) :
    -(9/160:ℝ) < refinedAffineJ n t := by
  let N : ℝ := n
  let z : ℝ := (17/50)*t*Real.log (2*N/t)
  let Q : ℝ := N*t^2*Real.sqrt t
  have hN : (1501:ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have harg : (1:ℝ)<2*N/t := by
    apply (lt_div_iff₀ ht0).2
    nlinarith
  have hlog : 0 < Real.log (2*N/t) := Real.log_pos harg
  have hz : 0 < z := by dsimp [z]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hcore := refinedAffine_logCube_core n hn ht0 ht.le
  change 70*z^3 ≤ Q at hcore
  have hExp := refinedAffine_exp_neg_061t_gt ht0.le ht.le
  have hmul := mul_le_mul_of_nonneg_left hcore
    (by norm_num : (0:ℝ) ≤ (67/1000)*(8/15))
  have hExpMul := mul_lt_mul_of_pos_left hExp
    (by dsimp [Q]; positivity : 0 < (67/1000:ℝ)*Q)
  have hnum : (5/2:ℝ) < (67/1000:ℝ)*70*(8/15) := by norm_num
  have hnumMul := mul_lt_mul_of_pos_right hnum (pow_pos hz 3)
  have hPositive : (5/2:ℝ)*z^3 <
      (67/1000:ℝ)*Q*Real.exp (-(61/100:ℝ)*t) := by
    nlinarith [hmul,hExpMul,hnumMul]
  have hpoly := refinedAffine_J_cubic_floor hz.le
  change -(9/160:ℝ) ≤
    (5/2:ℝ)*z^3-(11/40:ℝ)*z^2-(57/200:ℝ)*z at hpoly
  have hcalc : -(9/160:ℝ) <
      (67/1000:ℝ)*Q*Real.exp (-(61/100:ℝ)*t)-
        (285/1000:ℝ)*z-(275/1000:ℝ)*z^2 := by
    nlinarith [hPositive,hpoly]
  unfold refinedAffineJ
  convert hcalc using 1 <;> (dsimp [Q,z,N]; ring)

end SpringerLean

#print axioms SpringerLean.refinedAffineJ_floor
