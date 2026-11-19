import SpringerLean.Round1630EnergySplineCellBridge

namespace SpringerLean

/-- The explicit global spline has the tail value used by the energy
certificate. -/
theorem energyMultiplierSplineValue_eq_tail
    (t : ℝ) (ht : energyMultiplierKnotTime (21 : Fin 22) ≤ t) :
    energyMultiplierSplineValue t = energyMultiplierTailValue t := by
  obtain ⟨hchi,hf,hs⟩ := energyMultiplierSpline_tail t ht
  apply EnergyMultiplierValue.ext
  · rfl
  · exact hchi
  · exact hf
  · exact hs

end SpringerLean

#print axioms SpringerLean.energyMultiplierSplineValue_eq_tail
