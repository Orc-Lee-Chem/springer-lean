import SpringerLean.Round1634ActualExplicitRadialFlux

open Filter
open scoped Topology

namespace SpringerLean

theorem energyMultiplierKnotTime_last :
    energyMultiplierKnotTime (21 : Fin 22) = 1 := by
  norm_num [energyMultiplierKnotTime, energyMultiplierEndpointRaw,
    energyMultiplierNode]

/-- All three global energy multipliers are locally constant on the
open tail beyond the last knot. -/
theorem energyMultiplierSpline_derivs_on_tail
    (t : ℝ) (ht : 1 < t) :
    (DifferentiableAt ℝ energyMultiplierChi t ∧
      deriv energyMultiplierChi t = 0) ∧
    (DifferentiableAt ℝ energyMultiplierF t ∧
      deriv energyMultiplierF t = 0) ∧
    (DifferentiableAt ℝ energyMultiplierSigma t ∧
      deriv energyMultiplierSigma t = 0) := by
  have hnbd : Set.Ioi (1:ℝ) ∈ 𝓝 t :=
    isOpen_Ioi.mem_nhds ht
  have htail_t := energyMultiplierSpline_tail t
    (by rw [energyMultiplierKnotTime_last]; exact ht.le)
  have hchiLoc : energyMultiplierChi =ᶠ[𝓝 t]
      fun s => energyMultiplierChi t+(0:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have htail_s := energyMultiplierSpline_tail s
      (by rw [energyMultiplierKnotTime_last]; exact hs.le)
    simp [htail_s.1, htail_t.1]
  have hfLoc : energyMultiplierF =ᶠ[𝓝 t]
      fun s => energyMultiplierF t+(0:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have htail_s := energyMultiplierSpline_tail s
      (by rw [energyMultiplierKnotTime_last]; exact hs.le)
    simp [htail_s.2.1, htail_t.2.1]
  have hsLoc : energyMultiplierSigma =ᶠ[𝓝 t]
      fun s => energyMultiplierSigma t+(0:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have htail_s := energyMultiplierSpline_tail s
      (by rw [energyMultiplierKnotTime_last]; exact hs.le)
    simp [htail_s.2.2, htail_t.2.2]
  exact ⟨deriv_of_eventually_affine energyMultiplierChi t
      (energyMultiplierChi t) 0 hchiLoc,
    deriv_of_eventually_affine energyMultiplierF t
      (energyMultiplierF t) 0 hfLoc,
    deriv_of_eventually_affine energyMultiplierSigma t
      (energyMultiplierSigma t) 0 hsLoc⟩

end SpringerLean

#print axioms SpringerLean.energyMultiplierKnotTime_last
#print axioms SpringerLean.energyMultiplierSpline_derivs_on_tail
