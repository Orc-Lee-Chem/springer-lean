import SpringerLean.Round1631EnergySplineTailBridge

namespace SpringerLean

/-- The explicit continuous global spline is a genuine profile witness
for the original all-time endpoint certificate at every t ≥ 0. -/
theorem energyMultiplierSpline_profile_exists
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ cp fp sp : ℝ,
      EnergyMultiplierProfileAt t
        (energyMultiplierSplineValue t) cp fp sp := by
  rcases energyMultiplier_time_covered t ht with hcell | htail
  · obtain ⟨i, ht₀, ht₁⟩ := hcell
    obtain ⟨lam, hlam₀, hlam₁, htime⟩ :=
      energyMultiplier_cell_time_surjective i t ht₀ ht₁
    let r₀ := energyMultiplierEndpointRaw (2*i.val)
    have htimes := energyMultiplier_cell_endpoint_times i
    have hleft : energyMultiplierKnotTime i.castSucc ≤ t := by
      rw [← htimes.1]
      exact ht₀
    have hright : t ≤ energyMultiplierKnotTime i.succ := by
      rw [← htimes.2]
      exact ht₁
    have hv := energyMultiplierSplineValue_eq_cell i lam t
      htime hleft hright
    refine ⟨(r₀.cp:ℝ), (r₀.fp:ℝ), (r₀.sp:ℝ), ?_⟩
    refine ⟨rfl, Or.inl ?_⟩
    exact ⟨i, lam, hlam₀, hlam₁, hv, rfl, rfl, rfl⟩
  · let r := energyMultiplierEndpointRaw 42
    have hfinal : energyMultiplierKnotTime (21 : Fin 22) ≤ t := by
      simpa [energyMultiplierKnotTime] using htail
    have hv := energyMultiplierSplineValue_eq_tail t hfinal
    refine ⟨(r.cp:ℝ), (r.fp:ℝ), (r.sp:ℝ), ?_⟩
    refine ⟨rfl, Or.inr ?_⟩
    exact ⟨hv, rfl, rfl, rfl⟩

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_profile_exists
