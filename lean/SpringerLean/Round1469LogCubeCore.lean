import SpringerLean.Round1468LogCubeInN

namespace SpringerLean
set_option maxHeartbeats 200000

theorem logCube_base_70 :
    70*(17/50:ℝ)^3*(Real.log 3002)^3 < 1501 := by
  have hlog0 : 0 ≤ Real.log 3002 := by
    linarith [log_3002_gt_six]
  have hpow := pow_lt_pow_left₀ log_3002_lt_81_10 hlog0
    (by norm_num : (3:ℕ) ≠ 0)
  have hrat : 70*(17/50:ℝ)^3*(81/10:ℝ)^3 < 1501 := by norm_num
  have hh := mul_lt_mul_of_pos_left hpow
    (by norm_num : (0:ℝ)<70*(17/50:ℝ)^3)
  linarith

/-- The key scale-free inequality for the J floor, valid for every
order and every positive deficit in the localization range. -/
theorem refinedAffine_logCube_core
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 1) :
    70*((17/50:ℝ)*t*Real.log (2*(n:ℝ)/t))^3 ≤
      (n:ℝ)*t^2*Real.sqrt t := by
  let N : ℝ := n
  let L : ℝ := Real.log (2*N/t)
  let c : ℝ := Real.log (2*N)
  let c₀ : ℝ := Real.log 3002
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0<n)
  have htEnv := logCube_t_envelope n hn ht0 ht
  change Real.sqrt t*L^3 ≤ c^3 at htEnv
  have hnEnv := logCube_n_envelope n hn
  change c^3 ≤ (N/1501)*c₀^3 at hnEnv
  have hbase := logCube_base_70
  change 70*(17/50:ℝ)^3*c₀^3 < 1501 at hbase
  have hcoef : 0 ≤ 70*(17/50:ℝ)^3 := by norm_num
  have h1 := mul_le_mul_of_nonneg_left htEnv hcoef
  have h2 := mul_le_mul_of_nonneg_left hnEnv hcoef
  have h3 := mul_lt_mul_of_pos_left hbase
    (div_pos hN (by norm_num : (0:ℝ)<1501))
  have hcore : 70*(17/50:ℝ)^3*Real.sqrt t*L^3 < N := by
    have hcancel : (1501:ℝ)*(N/1501)=N := by ring
    nlinarith [h1,h2,h3,hcancel]
  have hroot : (Real.sqrt t)^2=t := Real.sq_sqrt ht0.le
  have hscale : 0 ≤ t^2*Real.sqrt t := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcore.le hscale
  change 70*(17/50:ℝ)^3*Real.sqrt t*L^3*
      (t^2*Real.sqrt t) ≤ N*(t^2*Real.sqrt t) at hmul
  have heq : 70*((17/50:ℝ)*t*L)^3 =
      70*(17/50:ℝ)^3*Real.sqrt t*L^3*
        (t^2*Real.sqrt t) := by
    calc
      70*((17/50:ℝ)*t*L)^3 =
          70*(17/50:ℝ)^3*(t^2*t)*L^3 := by ring
      _ = 70*(17/50:ℝ)^3*(t^2*(Real.sqrt t)^2)*L^3 := by
        rw [hroot]
      _ = 70*(17/50:ℝ)^3*Real.sqrt t*L^3*
          (t^2*Real.sqrt t) := by ring
  change 70*((17/50:ℝ)*t*L)^3 ≤ N*t^2*Real.sqrt t
  rw [heq]
  convert hmul using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.refinedAffine_logCube_core
