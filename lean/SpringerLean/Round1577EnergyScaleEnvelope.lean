import SpringerLean.Round1576EnergyEndpointRealQuadratic

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The only k-dependent fractional scale in the multiplier's mixed
absolute-value term lies between its limit and its k=751 value. -/
theorem energyMultiplier_scale_interval
    {k : ℕ} (hk : 751 ≤ k) :
    (1/4:ℝ) ≤ (k:ℝ)/(4*((k:ℝ)-1)) ∧
      (k:ℝ)/(4*((k:ℝ)-1)) ≤ 751/(4*750) := by
  have hkR : (751:ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 < (k:ℝ)-1 := by linarith
  constructor
  · apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<4)
        (by positivity : 0 < 4*((k:ℝ)-1))).2
    nlinarith
  · apply (div_le_div_iff₀ (by positivity : 0 < 4*((k:ℝ)-1))
        (by norm_num : (0:ℝ)<4*750)).2
    nlinarith

/-- The absolute value of a real affine term on an interval is bounded
by its larger endpoint value. This replaces all interior searches for
the mixed energy coefficient. -/
theorem abs_affine_interval_le_endpoint_max
    {a b x y : ℝ} (hay : a ≤ y) (hyb : y ≤ b) :
    |x-y| ≤ max |x-a| |x-b| := by
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le (x-b)
    have hm : |x-b| ≤ max |x-a| |x-b| := le_max_right _ _
    linarith
  · have h := le_abs_self (x-a)
    have hm : |x-a| ≤ max |x-a| |x-b| := le_max_left _ _
    linarith

/-- The same endpoint maximum controls an affine expression whose
direction reverses when the fixed slope is negative. -/
theorem abs_affine_scale_le_endpoint_max
    {lo hi x c r : ℝ} (hlo : lo ≤ r) (hhi : r ≤ hi) :
    |x-r*c| ≤ max |x-lo*c| |x-hi*c| := by
  by_cases hc : 0 ≤ c
  · exact abs_affine_interval_le_endpoint_max
      (mul_le_mul_of_nonneg_right hlo hc)
      (mul_le_mul_of_nonneg_right hhi hc)
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    have h1 := mul_le_mul_of_nonpos_right hhi hc'
    have h2 := mul_le_mul_of_nonpos_right hlo hc'
    have h := abs_affine_interval_le_endpoint_max (x := x) h1 h2
    simpa only [max_comm] using h

end SpringerLean

#print axioms SpringerLean.energyMultiplier_scale_interval
#print axioms SpringerLean.abs_affine_scale_le_endpoint_max
