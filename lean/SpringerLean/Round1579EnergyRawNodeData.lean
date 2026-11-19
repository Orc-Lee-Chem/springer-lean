import SpringerLean.Round1578EnergyKEnvelope

namespace SpringerLean
set_option maxHeartbeats 2000000

/-- The value and the selected one-sided slope at one of the 43
multiplier endpoint cases, in the paper's physical coordinates. -/
structure EnergyMultiplierEndpointRaw where
  t : ℚ
  chi : ℚ
  f : ℚ
  sigma : ℚ
  cp : ℚ
  fp : ℚ
  sp : ℚ

def energyMultiplierEndpointRaw (caseNo : ℕ) : EnergyMultiplierEndpointRaw := Id.run do
  let cell := if caseNo = 42 then 21 else caseNo/2
  let endpoint := if caseNo = 42 then 21 else cell+caseNo%2
  let u := energyMultiplierNode cell
  let w := energyMultiplierNode (cell+1)
  let v := energyMultiplierNode endpoint
  let cp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.chi w.chi u.i w.i
  let fp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.f w.f u.i w.i
  let sp : ℚ := if cell = 21 then 0 else
    energyMultiplierSlope u.sigma w.sigma u.i w.i
  return ⟨v.i/60,v.chi/1000000,v.f/1000000,
    v.sigma/1000000,cp,fp,sp⟩

/-- Each table value used in the uniform-k envelope is nonnegative;
the potentially signed quantities are only the one-sided slopes. -/
theorem energyMultiplierEndpointRaw_nonneg_all43 :
    ∀ j : Fin 43,
      0 ≤ (energyMultiplierEndpointRaw j).t ∧
      0 ≤ (energyMultiplierEndpointRaw j).chi ∧
      0 ≤ (energyMultiplierEndpointRaw j).f ∧
      0 ≤ (energyMultiplierEndpointRaw j).sigma := by
  intro j
  fin_cases j <;>
    norm_num [energyMultiplierEndpointRaw,energyMultiplierNode,
      energyMultiplierSlope]

end SpringerLean

#print axioms SpringerLean.energyMultiplierEndpointRaw_nonneg_all43
