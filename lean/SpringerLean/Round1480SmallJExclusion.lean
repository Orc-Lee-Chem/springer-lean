import SpringerLean.Round1479SmallIntervalCubicCore

namespace SpringerLean
set_option maxHeartbeats 220000

theorem refinedAffine_small_exp_lower
    {t : ℝ} (ht : t ≤ 3/20) :
    (1-(183/4000:ℝ))^2 ≤
      Real.exp (-(61/100:ℝ)*t) := by
  have hbase := refinedAffine_base_exp_lower
  have hmono : Real.exp (-(183/2000:ℝ)) ≤
      Real.exp (-(61/100:ℝ)*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact hbase.trans hmono

theorem refinedAffine_small_cubic_coefficient :
    (61/10:ℝ) < (67/1000:ℝ)*100*
      (1-(183/4000:ℝ))^2 := by norm_num

/-- A single polynomial bound excludes logarithmic width at least
`0.51`; the positive cubic dominates both width penalties. -/
theorem refinedAffine_small_cubic_excludes
    {z : ℝ} (hz : 51/100 ≤ z) :
    (58/100:ℝ) < (61/10:ℝ)*z^3-
      (285/1000:ℝ)*z-(275/1000:ℝ)*z^2 := by
  let u : ℝ := z-51/100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsq : 0 ≤ u^2 := sq_nonneg u
  have hcub : 0 ≤ u^3 := pow_nonneg hu 3
  have hnum : (58/100:ℝ) <
      (61/10:ℝ)*(51/100)^3-
      (285/1000:ℝ)*(51/100)-
      (275/1000:ℝ)*(51/100)^2 := by norm_num
  have hpoly : (61/10:ℝ)*z^3-
      (285/1000:ℝ)*z-(275/1000:ℝ)*z^2 =
      ((61/10:ℝ)*(51/100)^3-
        (285/1000:ℝ)*(51/100)-
        (275/1000:ℝ)*(51/100)^2)+
      u*((61/10:ℝ)*3*(51/100)^2-
        (285/1000:ℝ)-(275/1000:ℝ)*2*(51/100))+
      u^2*((61/10:ℝ)*3*(51/100)-(275/1000:ℝ))+
      (61/10:ℝ)*u^3 := by dsimp [u]; ring
  rw [hpoly]
  nlinarith

/-- This is the second localization exclusion, uniformly in the
unbounded order. It uses no endpoint geometry or finite certificate. -/
theorem refinedAffineJ_small_z_lt_051
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 3/20)
    (hJ : refinedAffineJ n t < 58/100) :
    (17/50:ℝ)*t*Real.log (2*(n:ℝ)/t) < 51/100 := by
  let z : ℝ := (17/50)*t*Real.log (2*(n:ℝ)/t)
  by_contra h
  have hz : (51/100:ℝ) ≤ z := by dsimp [z]; linarith
  have hcore := refinedAffine_small_logCube_core_100 n hn ht0 ht
  change 100*z^3 ≤ (n:ℝ)*t^2*Real.sqrt t at hcore
  have hexp := refinedAffine_small_exp_lower ht
  have hfactor := refinedAffine_small_cubic_coefficient
  have hmul1 := mul_le_mul_of_nonneg_left hcore
    (by norm_num : (0:ℝ) ≤ 67/1000)
  have hmul2 := mul_le_mul_of_nonneg_left hexp
    (by positivity : 0 ≤ (67/1000:ℝ)*(n:ℝ)*t^2*Real.sqrt t)
  have hmul3 := mul_lt_mul_of_pos_right hfactor (pow_pos (lt_of_lt_of_le (by norm_num : (0:ℝ)<51/100) hz) 3)
  have hpos : (61/10:ℝ)*z^3 <
      (67/1000:ℝ)*(n:ℝ)*t^2*Real.sqrt t*
        Real.exp (-(61/100:ℝ)*t) := by
    nlinarith [hmul1,hmul2,hmul3]
  have hpoly := refinedAffine_small_cubic_excludes hz
  unfold refinedAffineJ at hJ
  change (67/1000:ℝ)*(n:ℝ)*t^2*Real.sqrt t*
      Real.exp (-(61/100:ℝ)*t)-
      (285/1000:ℝ)*z-(275/1000:ℝ)*z^2 < 58/100 at hJ
  linarith

end SpringerLean

#print axioms SpringerLean.refinedAffineJ_small_z_lt_051
