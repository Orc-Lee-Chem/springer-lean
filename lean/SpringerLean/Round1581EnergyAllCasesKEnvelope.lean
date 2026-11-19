import SpringerLean.Round1580EnergyDataFormulaBridge

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The generic k-envelope now applies to every one of the 43
printed multiplier endpoints. The remaining bridge to the C=25/16
certificate is the rational-to-real identification of its baseline
triple, followed by interpolation between nodes. -/
theorem energyMultiplier_all43_k_envelope
    {k : ℕ} (hk : 751 ≤ k) (j : Fin 43) :
    let v := energyMultiplierEndpointRaw j
    let chi : ℝ := v.chi
    let f : ℝ := v.f
    let sigma : ℝ := v.sigma
    let cp : ℝ := v.cp
    let fp : ℝ := v.fp
    let sp : ℝ := v.sp
    let t : ℝ := v.t
    let h := f+t*fp
    let Q := 2*max (0:ℝ) f+2*|h|+t*|sp|+sigma
    let P := |h|+t*|sp|/2+sigma
    chi+fp-|sp|/2-Q/751 ≤
      chi+fp-|sp|/2-Q/(k:ℝ) ∧
    ((k:ℝ)*chi+t*|cp|)/(4*((k:ℝ)-1)) ≤
      (751*chi+t*|cp|)/(4*750) ∧
    |chi-sigma|+|2*f-((k:ℝ)/(4*((k:ℝ)-1)))*cp|+
        t*|cp|/(2*((k:ℝ)-1))+P/(k:ℝ) ≤
      |chi-sigma|+
        max |2*f-cp/4| |2*f-(751/(4*750):ℝ)*cp|+
        t*|cp|/(2*750)+P/751 := by
  dsimp only
  let v := energyMultiplierEndpointRaw j
  obtain ⟨ht, hchi, hf, hsigma⟩ := energyMultiplierEndpointRaw_nonneg_all43 j
  have htR : (0:ℝ) ≤ v.t := by exact_mod_cast ht
  have hchiR : (0:ℝ) ≤ v.chi := by exact_mod_cast hchi
  have hfR : (0:ℝ) ≤ v.f := by exact_mod_cast hf
  have hsigmaR : (0:ℝ) ≤ v.sigma := by exact_mod_cast hsigma
  have hQ : 0 ≤ 2*max (0:ℝ) (v.f:ℝ)+
      2*|(v.f:ℝ)+(v.t:ℝ)*(v.fp:ℝ)|+
      (v.t:ℝ)*|(v.sp:ℝ)|+(v.sigma:ℝ) := by positivity
  have hP : 0 ≤ |(v.f:ℝ)+(v.t:ℝ)*(v.fp:ℝ)|+
      (v.t:ℝ)*|(v.sp:ℝ)|/2+(v.sigma:ℝ) := by positivity
  exact energyMultiplier_coefficients_k_envelope hk hchiR htR hQ hP

end SpringerLean

#print axioms SpringerLean.energyMultiplier_all43_k_envelope
