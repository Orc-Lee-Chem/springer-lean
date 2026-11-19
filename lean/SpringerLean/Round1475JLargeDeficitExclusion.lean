import SpringerLean.Round1474NormalizedLogBounds

namespace SpringerLean
set_option maxHeartbeats 250000

/-- The base logarithm is below ten. This is exactly the `z₀=0.51`
base-point computation in a form suited to order normalization. -/
theorem refinedAffine_base_log_lt_ten :
    Real.log (2*(1501:ℝ)/(3/20:ℝ)) < 10 := by
  have h := refinedAffine_base_z_lt_051
  nlinarith

/-- At every order `n≥1501`, the part `t≥3/20` is incompatible with
the individual `J<0.58` constraint. -/
theorem refinedAffineJ_large_deficit_gt_058
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : (3/20:ℝ) ≤ t) (ht1 : t ≤ 1) :
    (58/100:ℝ) < refinedAffineJ n t := by
  let N : ℝ := n
  let L : ℝ := Real.log (2*N/t)
  let z : ℝ := (17/50)*t*L
  let g : ℝ := Real.sqrt t*Real.exp (-(61/100:ℝ)*t)
  let g₀ : ℝ := Real.sqrt (3/20:ℝ)*
    Real.exp (-(61/100:ℝ)*(3/20:ℝ))
  let q : ℝ := N*t^2
  let q₀ : ℝ := 1501*(3/20:ℝ)^2
  let r : ℝ := q/q₀
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have ht : 0 < t := by linarith
  have hL0 : 0 ≤ L := by
    dsimp [L]
    apply Real.log_nonneg
    apply (le_div_iff₀ ht).2
    nlinarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hq0 : 0 < q₀ := by dsimp [q₀]; norm_num
  have hr : 1 ≤ r := by
    dsimp [r,q,q₀]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<1501*(3/20:ℝ)^2)).2
    nlinarith [sq_nonneg (t-3/20)]
  have hg : g₀ ≤ g := refinedAffine_positive_interval ht0 ht1
  have hlog := refinedAffine_log_over_order_bound n hn ht0
  change L/N ≤ Real.log (2*(1501:ℝ)/(3/20:ℝ))/1501 at hlog
  have hbaseLog := refinedAffine_base_log_lt_ten
  have hLorder : L ≤ N*10/1501 := by
    have hh : L/N < 10/1501 := by linarith
    have hmul := mul_lt_mul_of_pos_right hh hN0
    nlinarith [div_mul_cancel₀ L (ne_of_gt hN0)]
  have hlogsq := refinedAffine_log_sq_over_order_bound n hn ht0 ht1
  change L^2/N ≤
    (Real.log (2*(1501:ℝ)/(3/20:ℝ)))^2/1501 at hlogsq
  have hbaseLog0 : 0 ≤ Real.log (2*(1501:ℝ)/(3/20:ℝ)) := by
    apply Real.log_nonneg
    norm_num
  have hbaseSq := pow_le_pow_left₀ hbaseLog0 hbaseLog.le 2
  have hLsq : L^2 ≤ N*100/1501 := by
    have hh : L^2/N ≤ 100/1501 := by nlinarith [hlogsq,hbaseSq]
    have hmul := mul_le_mul_of_nonneg_right hh hN0.le
    nlinarith [div_mul_cancel₀ (L^2) (ne_of_gt hN0)]
  have htscale : t ≤ t^2/(3/20:ℝ) := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<3/20)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr ht0) (le_of_lt ht)]
  have hz : z ≤ r*(51/100:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hLorder
      (by positivity : 0 ≤ (17/50:ℝ)*t)
    have hmul2 := mul_le_mul_of_nonneg_left htscale
      (by positivity : 0 ≤ (17/50:ℝ)*N*10/1501)
    calc
      z = (17/50:ℝ)*t*L := rfl
      _ ≤ (17/50:ℝ)*t*(N*10/1501) := hmul
      _ = (17/50:ℝ)*N*10/1501*t := by ring
      _ ≤ (17/50:ℝ)*N*10/1501*(t^2/(3/20:ℝ)) := hmul2
      _ = r*(51/100:ℝ) := by dsimp [r,q,q₀]; ring
  have hzsq : z^2 ≤ r*(51/100:ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hLsq
      (sq_nonneg ((17/50:ℝ)*t))
    calc
      z^2 = ((17/50:ℝ)*t)^2*L^2 := by dsimp [z]; ring
      _ ≤ ((17/50:ℝ)*t)^2*(N*100/1501) := hmul
      _ = r*(51/100:ℝ)^2 := by dsimp [r,q,q₀]; ring
  have hpos : (67/1000:ℝ)*q*g₀ ≤ (67/1000:ℝ)*q*g := by
    exact mul_le_mul_of_nonneg_left hg (by dsimp [q]; positivity)
  have hbase : (58/100:ℝ) < (67/1000:ℝ)*q₀*g₀-
      (285/1000:ℝ)*(51/100)-(275/1000:ℝ)*(51/100)^2 := by
    convert refinedAffine_J_base_gt_058 using 1 <;>
      (dsimp [q₀,g₀]; norm_num; ring)
  have hscaled := mul_lt_mul_of_pos_left hbase
    (by dsimp [r]; positivity : 0 < r)
  have hqeq : r*q₀=q := by dsimp [r]; field_simp
  have hpositiveEq : r*((67/1000:ℝ)*q₀*g₀) =
      (67/1000:ℝ)*q*g₀ := by
    calc
      _ = (67/1000:ℝ)*(r*q₀)*g₀ := by ring
      _ = (67/1000:ℝ)*q*g₀ := by rw [hqeq]
  have hscaled' : r*(58/100:ℝ) <
      (67/1000:ℝ)*q*g₀-
      r*((285/1000:ℝ)*(51/100))-
      r*((275/1000:ℝ)*(51/100)^2) := by
    linarith [hscaled,hpositiveEq]
  have hneg1 : (285/1000:ℝ)*z ≤
      r*((285/1000:ℝ)*(51/100)) := by
    nlinarith [hz]
  have hneg2 : (275/1000:ℝ)*z^2 ≤
      r*((275/1000:ℝ)*(51/100)^2) := by
    nlinarith [hzsq]
  have hr58 : (58/100:ℝ) ≤ r*(58/100:ℝ) := by nlinarith
  have hcalc : (58/100:ℝ) <
      (67/1000:ℝ)*q*g-
      (285/1000:ℝ)*z-(275/1000:ℝ)*z^2 := by
    linarith
  unfold refinedAffineJ
  convert hcalc using 1 <;> (dsimp [q,g,z,L,N]; ring)

end SpringerLean

#print axioms SpringerLean.refinedAffineJ_large_deficit_gt_058
