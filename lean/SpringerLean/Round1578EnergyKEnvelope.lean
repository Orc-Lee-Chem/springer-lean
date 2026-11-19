import SpringerLean.Round1577EnergyScaleEnvelope

namespace SpringerLean
set_option maxHeartbeats 640000

/-- A uniform k-envelope for the three multiplier coefficients at a
fixed point and fixed one-sided slope. The two absolute endpoint
values in B correspond to scales 1/4 and 751/(4*750). -/
theorem energyMultiplier_coefficients_k_envelope
    {k : ℕ} (hk : 751 ≤ k)
    {chi f sigma cp fp sp t Q P : ℝ}
    (hchi : 0 ≤ chi) (ht : 0 ≤ t)
    (hQ : 0 ≤ Q) (hP : 0 ≤ P) :
    chi+fp-|sp|/2-Q/751 ≤
      chi+fp-|sp|/2-Q/(k:ℝ) ∧
    ((k:ℝ)*chi+t*|cp|)/(4*((k:ℝ)-1)) ≤
      (751*chi+t*|cp|)/(4*750) ∧
    |chi-sigma|+|2*f-((k:ℝ)/(4*((k:ℝ)-1)))*cp|+
        t*|cp|/(2*((k:ℝ)-1))+P/(k:ℝ) ≤
      |chi-sigma|+
        max |2*f-cp/4| |2*f-(751/(4*750):ℝ)*cp|+
        t*|cp|/(2*750)+P/751 := by
  have hkR : (751:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hkm : 0 < (k:ℝ)-1 := by linarith
  have hQdiv : Q/(k:ℝ) ≤ Q/751 := by
    apply (div_le_div_iff₀ hk0 (by norm_num : (0:ℝ)<751)).2
    nlinarith [mul_nonneg hQ (sub_nonneg.mpr hkR)]
  have hPdiv : P/(k:ℝ) ≤ P/751 := by
    apply (div_le_div_iff₀ hk0 (by norm_num : (0:ℝ)<751)).2
    nlinarith [mul_nonneg hP (sub_nonneg.mpr hkR)]
  have hscale := energyMultiplier_scale_interval hk
  have hchiScale := mul_le_mul_of_nonneg_left hscale.2 hchi
  have hT0 : 0 ≤ t*|cp| := mul_nonneg ht (abs_nonneg _)
  have hTdiv : t*|cp|/(4*((k:ℝ)-1)) ≤ t*|cp|/(4*750) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*((k:ℝ)-1))
      (by norm_num : (0:ℝ)<4*750)).2
    nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hkR)]
  have hTdiv2 : t*|cp|/(2*((k:ℝ)-1)) ≤ t*|cp|/(2*750) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*((k:ℝ)-1))
      (by norm_num : (0:ℝ)<2*750)).2
    nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hkR)]
  have hmixed := abs_affine_scale_le_endpoint_max
    (x := 2*f) (c := cp) hscale.1 hscale.2
  rw [show (1/4:ℝ)*cp = cp/4 by ring] at hmixed
  constructor
  · linarith
  constructor
  · have hrewrite :
        ((k:ℝ)*chi+t*|cp|)/(4*((k:ℝ)-1)) =
        chi*((k:ℝ)/(4*((k:ℝ)-1)))+
          t*|cp|/(4*((k:ℝ)-1)) := by ring
    rw [hrewrite]
    have hbase : (751*chi+t*|cp|)/(4*750) =
        chi*(751/(4*750):ℝ)+t*|cp|/(4*750) := by ring
    rw [hbase]
    linarith
  · linarith [hmixed,hTdiv2,hPdiv]

end SpringerLean

#print axioms SpringerLean.energyMultiplier_coefficients_k_envelope
