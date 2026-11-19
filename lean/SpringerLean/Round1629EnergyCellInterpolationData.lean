import SpringerLean.Round1628EnergyMultiplierTailValues

namespace SpringerLean

/-- The two one-sided endpoints of each printed cell have the exact
coordinate increment prescribed by the cell slope. -/
theorem energyMultiplier_cell_endpoint_increments (i : Fin 21) :
    let r₀ := energyMultiplierEndpointRaw (2*i.val)
    let r₁ := energyMultiplierEndpointRaw (2*i.val+1)
    let width := r₁.t-r₀.t
    ((r₀.cp:ℚ):ℝ)*width = (r₁.chi:ℝ)-(r₀.chi:ℝ) ∧
    ((r₀.fp:ℚ):ℝ)*width = (r₁.f:ℝ)-(r₀.f:ℝ) ∧
    ((r₀.sp:ℚ):ℝ)*width = (r₁.sigma:ℝ)-(r₀.sigma:ℝ) := by
  fin_cases i <;>
    norm_num [energyMultiplierEndpointRaw, energyMultiplierNode,
      energyMultiplierSlope]

/-- The two coordinates of one printed cell are exactly the two
consecutive knot times of the global spline. -/
theorem energyMultiplier_cell_endpoint_times (i : Fin 21) :
    (energyMultiplierEndpointRaw (2*i.val)).t =
      energyMultiplierKnotTime i.castSucc ∧
    (energyMultiplierEndpointRaw (2*i.val+1)).t =
      energyMultiplierKnotTime i.succ := by
  fin_cases i <;>
    norm_num [energyMultiplierKnotTime, energyMultiplierEndpointRaw,
      energyMultiplierNode]

end SpringerLean

#print axioms SpringerLean.energyMultiplier_cell_endpoint_increments
#print axioms SpringerLean.energyMultiplier_cell_endpoint_times
