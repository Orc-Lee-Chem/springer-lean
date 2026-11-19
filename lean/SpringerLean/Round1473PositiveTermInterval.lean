import SpringerLean.Round1472JBasePoint

namespace SpringerLean
set_option maxHeartbeats 250000

/-- On the lower part of the localization interval the logarithmic
gain of `t` pays the exponential loss. -/
theorem refinedAffine_positive_interval_low
    {t : ℝ} (ht0 : (3/20:ℝ) ≤ t) (ht1 : t ≤ 3/5) :
    (3/20:ℝ)*Real.exp (-(61/50:ℝ)*(3/20:ℝ)) ≤
      t*Real.exp (-(61/50:ℝ)*t) := by
  have ht : 0 < t := by linarith
  have hrec : 0 < (3/20:ℝ)/t := div_pos (by norm_num) ht
  have hlog := Real.log_le_sub_one_of_pos hrec
  have hlog' : Real.log (t/(3/20:ℝ)) ≥ 1-(3/20:ℝ)/t := by
    rw [Real.log_div (by norm_num : (3/20:ℝ) ≠ 0) ht.ne'] at hlog
    rw [Real.log_div ht.ne' (by norm_num : (3/20:ℝ) ≠ 0)]
    linarith
  have hquad : (61/50:ℝ)*(t-3/20) ≤ 1-(3/20:ℝ)/t := by
    have hdiv : 1-(3/20:ℝ)/t = (t-3/20)/t := by field_simp
    rw [hdiv]
    apply (le_div_iff₀ ht).2
    have hgap : 0 ≤ t-3/20 := by linarith
    have hcoef : (61/50:ℝ)*t ≤ 1 := by nlinarith
    nlinarith
  have hloggap : (61/50:ℝ)*(t-3/20) ≤
      Real.log (t/(3/20:ℝ)) := le_trans hquad hlog'
  have hexp := Real.exp_le_exp.mpr hloggap
  rw [Real.exp_log (div_pos ht (by norm_num : (0:ℝ)<3/20))] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp
    (le_of_lt (Real.exp_pos (-(61/50:ℝ)*t)))
  have hidentity :
      (3/20:ℝ)*Real.exp ((61/50:ℝ)*(t-3/20))*
        Real.exp (-(61/50:ℝ)*t) =
      (3/20:ℝ)*Real.exp (-(61/50:ℝ)*(3/20:ℝ)) := by
    calc
      _ = (3/20:ℝ)*(Real.exp ((61/50:ℝ)*(t-3/20))*
          Real.exp (-(61/50:ℝ)*t)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hscale := mul_le_mul_of_nonneg_left hmul
    (by norm_num : (0:ℝ) ≤ 3/20)
  have hdiv : (3/20:ℝ)*(t/(3/20:ℝ))*
      Real.exp (-(61/50:ℝ)*t) =
      t*Real.exp (-(61/50:ℝ)*t) := by ring
  calc
    (3/20:ℝ)*Real.exp (-(61/50:ℝ)*(3/20:ℝ)) =
        (3/20:ℝ)*(Real.exp ((61/50:ℝ)*(t-3/20))*
          Real.exp (-(61/50:ℝ)*t)) := by rw [←mul_assoc, hidentity]
    _ ≤ (3/20:ℝ)*((t/(3/20:ℝ))*
          Real.exp (-(61/50:ℝ)*t)) := hscale
    _ = t*Real.exp (-(61/50:ℝ)*t) := by rw [←mul_assoc, hdiv]

/-- A coarse rational reserve on the upper part of the interval.
The split at `3/5` avoids differentiating the square-root exponential. -/
theorem refinedAffine_positive_interval_high
    {t : ℝ} (ht0 : (3/5:ℝ) ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (3/20:ℝ)*Real.exp (-(61/100:ℝ)*(3/20:ℝ)) <
      Real.sqrt t*Real.exp (-(61/100:ℝ)*t) := by
  have ht : 0 ≤ t := by linarith
  have hsqt : (Real.sqrt t)^2=t := Real.sq_sqrt ht
  have hsqrt : (3/4:ℝ) < Real.sqrt t := by
    nlinarith [Real.sqrt_nonneg t]
  have hsbase : Real.sqrt (3/20:ℝ) < 39/100 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/20),
      Real.sqrt_nonneg (3/20:ℝ)]
  have he : (1-(61/300:ℝ))^3 ≤ Real.exp (-(61/100:ℝ)) := by
    have h := Real.add_one_le_exp (-(61/300:ℝ))
    have hp := pow_le_pow_left₀
      (by norm_num : (0:ℝ) ≤ 1-61/300)
      (by linarith : (1-61/300:ℝ) ≤ Real.exp (-(61/300:ℝ))) 3
    have heq : Real.exp (-(61/100:ℝ)) =
        (Real.exp (-(61/300:ℝ)))^3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [heq]
    exact hp
  have hehalf : (1/2:ℝ) < Real.exp (-(61/100:ℝ)) := by
    have hnum : (1/2:ℝ) < (1-61/300:ℝ)^3 := by norm_num
    linarith
  have het : Real.exp (-(61/100:ℝ)) ≤
      Real.exp (-(61/100:ℝ)*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hbase_exp : Real.exp (-(61/100:ℝ)*(3/20:ℝ)) < 47/50 := by
    have hx := Real.add_one_le_exp ((61/100:ℝ)*(3/20:ℝ))
    have hpos := Real.exp_pos (-(61/100:ℝ)*(3/20:ℝ))
    have hprod : Real.exp ((61/100:ℝ)*(3/20:ℝ))*
        Real.exp (-(61/100:ℝ)*(3/20:ℝ))=1 := by
      rw [←Real.exp_add]
      norm_num
    nlinarith
  have hright : (3/8:ℝ) < Real.sqrt t*
      Real.exp (-(61/100:ℝ)*t) := by
    nlinarith [Real.exp_pos (-(61/100:ℝ)*t)]
  have hleft : Real.sqrt (3/20:ℝ)*
      Real.exp (-(61/100:ℝ)*(3/20:ℝ)) < 3/8 := by
    nlinarith [Real.exp_pos (-(61/100:ℝ)*(3/20:ℝ))]
  linarith

/-- The positive normalized moving-chord term never falls below its
value at the base deficit on the full excluded interval. -/
theorem refinedAffine_positive_interval
    {t : ℝ} (ht0 : (3/20:ℝ) ≤ t) (ht1 : t ≤ 1) :
    Real.sqrt (3/20:ℝ)*Real.exp (-(61/100:ℝ)*(3/20:ℝ)) ≤
      Real.sqrt t*Real.exp (-(61/100:ℝ)*t) := by
  by_cases h : t ≤ 3/5
  · have hsq := refinedAffine_positive_interval_low ht0 h
    have hroot0 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3/20)
    have hroot := Real.sq_sqrt (by linarith : 0 ≤ t)
    have hpos0 : 0 ≤ Real.sqrt (3/20:ℝ)*
        Real.exp (-(61/100:ℝ)*(3/20:ℝ)) := by positivity
    have hpos : 0 ≤ Real.sqrt t*Real.exp (-(61/100:ℝ)*t) := by positivity
    have hsquare :
        (Real.sqrt (3/20:ℝ)*Real.exp (-(61/100:ℝ)*(3/20:ℝ)))^2 =
          (3/20:ℝ)*Real.exp (-(61/50:ℝ)*(3/20:ℝ)) := by
      rw [mul_pow, hroot0, ←Real.exp_nat_mul]
      congr 1
      ring
    have hsquare' :
        (Real.sqrt t*Real.exp (-(61/100:ℝ)*t))^2 =
          t*Real.exp (-(61/50:ℝ)*t) := by
      rw [mul_pow, hroot, ←Real.exp_nat_mul]
      congr 1
      ring
    nlinarith
  · exact (refinedAffine_positive_interval_high (by linarith) ht1).le

end SpringerLean

#print axioms SpringerLean.refinedAffine_positive_interval
