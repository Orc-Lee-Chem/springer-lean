import SpringerLean.Round1478SmallIntervalLogEnvelopes

namespace SpringerLean
set_option maxHeartbeats 250000

/-- The stronger cubic logarithm core on the small-deficit interval.
This constant is exactly what excludes a logarithmic width `z≥0.51`. -/
theorem refinedAffine_small_logCube_core_100
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 3/20) :
    100*((17/50:ℝ)*t*Real.log (2*(n:ℝ)/t))^3 ≤
      (n:ℝ)*t^2*Real.sqrt t := by
  let N : ℝ := n
  let L : ℝ := Real.log (2*N/t)
  let c : ℝ := Real.log (2*N/(3/20:ℝ))
  let c₀ : ℝ := Real.log (2*(1501:ℝ)/(3/20:ℝ))
  let r₀ : ℝ := Real.sqrt (3/20:ℝ)
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have htEnv := refinedAffine_small_log_t_envelope n hn ht0 ht
  change Real.sqrt t*L^3 ≤ r₀*c^3 at htEnv
  have hnEnv := refinedAffine_small_log_n_envelope n hn
  change c^3 ≤ (N/1501)*c₀^3 at hnEnv
  have hbase := refinedAffine_small_base_core_100
  change 100*(17/50:ℝ)^3*r₀*c₀^3 < 1501 at hbase
  have hcoef : 0 ≤ 100*(17/50:ℝ)^3 := by norm_num
  have h1 := mul_le_mul_of_nonneg_left htEnv hcoef
  have h2 := mul_le_mul_of_nonneg_left hnEnv
    (by dsimp [r₀]; positivity : 0 ≤ 100*(17/50:ℝ)^3*r₀)
  have h3 := mul_lt_mul_of_pos_left hbase
    (div_pos hN0 (by norm_num : (0:ℝ)<1501))
  have hcore : 100*(17/50:ℝ)^3*Real.sqrt t*L^3 < N := by
    have hcancel : (1501:ℝ)*(N/1501)=N := by ring
    nlinarith [h1,h2,h3,hcancel]
  have hroot : (Real.sqrt t)^2=t := Real.sq_sqrt ht0.le
  have hscale : 0 ≤ t^2*Real.sqrt t := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcore.le hscale
  change 100*(17/50:ℝ)^3*Real.sqrt t*L^3*
      (t^2*Real.sqrt t) ≤ N*(t^2*Real.sqrt t) at hmul
  have heq : 100*((17/50:ℝ)*t*L)^3 =
      100*(17/50:ℝ)^3*Real.sqrt t*L^3*
        (t^2*Real.sqrt t) := by
    calc
      100*((17/50:ℝ)*t*L)^3 =
          100*(17/50:ℝ)^3*(t^2*t)*L^3 := by ring
      _ = 100*(17/50:ℝ)^3*(t^2*(Real.sqrt t)^2)*L^3 := by rw [hroot]
      _ = 100*(17/50:ℝ)^3*Real.sqrt t*L^3*
          (t^2*Real.sqrt t) := by ring
  change 100*((17/50:ℝ)*t*L)^3 ≤ N*t^2*Real.sqrt t
  rw [heq]
  convert hmul using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.refinedAffine_small_logCube_core_100
