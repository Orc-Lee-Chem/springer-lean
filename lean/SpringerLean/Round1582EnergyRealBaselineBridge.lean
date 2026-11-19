import SpringerLean.Round1581EnergyAllCasesKEnvelope

namespace SpringerLean
set_option maxHeartbeats 2000000

/-- The exact rational certificate triple agrees, case by case, with
the real baseline formulas used by the uniform-k envelope. -/
theorem energyMultiplier_all43_real_baseline_eq (j : Fin 43) :
    let v := energyMultiplierEndpointRaw j
    let (A,D,B) := energyMultiplierEndpointCoeffs j
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
    (A:ℝ) = chi+fp-|sp|/2-Q/751 ∧
    (D:ℝ) = (751*chi+t*|cp|)/(4*750) ∧
    (B:ℝ) = |chi-sigma|+
      max |2*f-cp/4| |2*f-(751/(4*750):ℝ)*cp|+
        t*|cp|/(2*750)+P/751 := by
  fin_cases j <;>
    norm_num [energyMultiplierEndpointCoeffs,
      energyMultiplierEndpointRaw,energyMultiplierNode,
      energyMultiplierSlope]

end SpringerLean

#print axioms SpringerLean.energyMultiplier_all43_real_baseline_eq
