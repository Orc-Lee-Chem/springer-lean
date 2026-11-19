import SpringerLean.Round1547ThinAnnulusPowerFactor

namespace SpringerLean
set_option maxHeartbeats 640000

/-- A rational square-root bound packages the factor
`(9/10)^(5/2)>3/4` without real powers. -/
theorem thinAnnulus_five_half_lower
    {d v : ℝ} (hd0 : 0 < d) (hv : (9/10:ℝ)*d ≤ v) :
    (3/4:ℝ)*d^2*Real.sqrt d ≤ v^2*Real.sqrt v := by
  have hv0 : 0 ≤ v := by linarith
  have hs0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have ht0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hs2 : (Real.sqrt d)^2=d := Real.sq_sqrt hd0.le
  have ht2 : (Real.sqrt v)^2=v := Real.sq_sqrt hv0
  have hsqrt : (25/27:ℝ)*Real.sqrt d ≤ Real.sqrt v := by
    have hsq : ((25/27:ℝ)*Real.sqrt d)^2 ≤
        (Real.sqrt v)^2 := by
      nlinarith [hv,hs2,ht2]
    nlinarith [hsq]
  have hsq : ((9/10:ℝ)*d)^2 ≤ v^2 :=
    pow_le_pow_left₀ (by positivity) hv 2
  have hmul1 := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (25/27:ℝ)*Real.sqrt d by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ v^2 by positivity)
  nlinarith [hmul1,hmul2]

/-- Retain more than 9/10 of the uncut model's `(2r)^(m-2)` factor
throughout the actual outer annulus. -/
theorem thinAnnulus_qpow_lower
    {m : ℕ} (hm : 1500 ≤ m) {d r : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20)
    (hrband : 1-Real.sqrt d/16 ≤ r) (hr1 : r ≤ 1) :
    let v := d-(3/2:ℝ)*(1-r)*Real.sqrt d
    (9/10:ℝ)*(2*r)^(m-2) ≤ (2*r-v)^(m-2) := by
  dsimp only
  let v : ℝ := d-(3/2:ℝ)*(1-r)*Real.sqrt d
  have hb := thinAnnulus_peak_parameter_bounds hm hd0 hD hrband hr1
  have hr0 : 0 < r := by dsimp only at hb; linarith [hb.2.2]
  have hfactor := thinAnnulus_power_factor_gt_nine_tenths
    hm hd0 hD hrband hr1
  dsimp only at hfactor
  have hmul := mul_le_mul_of_nonneg_left hfactor.le
    (show 0 ≤ (2*r)^(m-2) by positivity)
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hq : 2*r-v = (2*r)*(1-v/(2*r)) := by
    field_simp
  rw [hq,mul_pow]
  dsimp [v] at *
  simpa [mul_pow,mul_comm,mul_left_comm,mul_assoc] using hmul

end SpringerLean

#print axioms SpringerLean.thinAnnulus_five_half_lower
#print axioms SpringerLean.thinAnnulus_qpow_lower
