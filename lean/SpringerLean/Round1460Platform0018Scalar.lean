import SpringerLean.Round1459CandidateMoment0502

namespace SpringerLean
set_option maxHeartbeats 150000

/-- The plateau cost has far more than the required `0.018` reserve
once the order is at least 1501. -/
theorem refinedAffine_platform_scalar_0018
    (n : ℕ) (hn : 1501 ≤ n) :
    4*(n:ℝ)^2*(19/20:ℝ)^n < 18/1000 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hr : (19/20:ℝ)^20 ≤ 1/2 := by norm_num
    have hpow : ((19/20:ℝ)^20)^75 ≤ (1/2:ℝ)^75 :=
      pow_le_pow_left₀ (by positivity) hr 75
    have hsmall : (19/20:ℝ)^1501 ≤ (1/2:ℝ)^75 := by
      have heq : (19/20:ℝ)^1501 =
          ((19/20:ℝ)^20)^75*(19/20:ℝ) := by
        rw [←pow_mul,pow_succ]
      rw [heq]
      have hnonneg : 0 ≤ ((19/20:ℝ)^20)^75 := by positivity
      nlinarith [hpow]
    have hnum : 9012004*(1/2:ℝ)^75 < 9/500 := by norm_num
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (by norm_num : (0:ℝ) ≤ 9012004)
    have hh : 9012004*(19/20:ℝ)^1501 < 9/500 :=
      lt_of_le_of_lt hmul hnum
    convert hh using 1 <;> norm_num
  | succ m hm ih =>
    have hmR : (1501:ℝ) ≤ m := by exact_mod_cast hm
    have hmono : (((m:ℝ)+1)^2)*(19/20:ℝ) ≤ (m:ℝ)^2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m)
        (by linarith : (0:ℝ) ≤ (m:ℝ)-39)]
    have hpow : 0 ≤ (19/20:ℝ)^m := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hmono hpow
    rw [Nat.cast_add,Nat.cast_one,pow_succ (19/20:ℝ) m]
    nlinarith [hscaled]

end SpringerLean

#print axioms SpringerLean.refinedAffine_platform_scalar_0018
