import SpringerLean.Round1579EnergyRawNodeData

namespace SpringerLean
set_option maxHeartbeats 2000000

/-- The raw node and slope data reconstruct exactly the A,D,B triple
whose 43 discriminants were checked in Round1575. -/
theorem energyMultiplierEndpointRaw_coefficients_eq (j : Fin 43) :
    let v := energyMultiplierEndpointRaw j
    let h := v.f+v.t*v.fp
    let Q := 2*max (0:ℚ) v.f+2*|h|+v.t*|v.sp|+v.sigma
    let P := |h|+v.t*|v.sp|/2+v.sigma
    energyMultiplierEndpointCoeffs j =
      (v.chi+v.fp-|v.sp|/2-Q/751,
       (751*v.chi+v.t*|v.cp|)/(4*750),
       |v.chi-v.sigma|+
         max |2*v.f-v.cp/4| |2*v.f-(751/(4*750):ℚ)*v.cp|+
         v.t*|v.cp|/(2*750)+P/751) := by
  rfl

end SpringerLean

#print axioms SpringerLean.energyMultiplierEndpointRaw_coefficients_eq
