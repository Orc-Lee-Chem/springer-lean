import SpringerLean.Round1619EnergyRampPieces

namespace SpringerLean

/-- Each printed cell slope times its length is exactly the printed
coordinate increment. This connects the global spline to the table. -/
theorem energyMultiplier_cell_increments (i : Fin 21) :
    let r₀ := energyMultiplierEndpointRaw (2*i.val)
    let r₁ := energyMultiplierEndpointRaw (2*(i.val+1))
    let width := energyMultiplierKnotTime i.succ -
      energyMultiplierKnotTime i.castSucc
    ((r₀.cp:ℚ):ℝ)*width = (r₁.chi:ℝ)-(r₀.chi:ℝ) ∧
    ((r₀.fp:ℚ):ℝ)*width = (r₁.f:ℝ)-(r₀.f:ℝ) ∧
    ((r₀.sp:ℚ):ℝ)*width = (r₁.sigma:ℝ)-(r₀.sigma:ℝ) := by
  fin_cases i <;>
    norm_num [energyMultiplierKnotTime, energyMultiplierEndpointRaw,
      energyMultiplierNode, energyMultiplierSlope]

end SpringerLean

#print axioms SpringerLean.energyMultiplier_cell_increments
