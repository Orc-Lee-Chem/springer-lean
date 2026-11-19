import SpringerLean.Round1625EnergySplineCellValues

open Filter
open scoped Topology

namespace SpringerLean

/-- On every open printed cell, all three global multiplier curves
have the exact one-sided slopes used in the endpoint certificate. -/
theorem energyMultiplierSpline_derivs_on_open_cell
    (j : Fin 21) (t : ℝ)
    (hleft : energyMultiplierKnotTime j.castSucc < t)
    (hright : t < energyMultiplierKnotTime j.succ) :
    let r := energyMultiplierEndpointRaw (2*j.val)
    (DifferentiableAt ℝ energyMultiplierChi t ∧
      deriv energyMultiplierChi t = (r.cp:ℝ)) ∧
    (DifferentiableAt ℝ energyMultiplierF t ∧
      deriv energyMultiplierF t = (r.fp:ℝ)) ∧
    (DifferentiableAt ℝ energyMultiplierSigma t ∧
      deriv energyMultiplierSigma t = (r.sp:ℝ)) := by
  let r := energyMultiplierEndpointRaw (2*j.val)
  let a := energyMultiplierKnotTime j.castSucc
  let b := energyMultiplierKnotTime j.succ
  have hnbd : Set.Ioo a b ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨hleft, hright⟩
  have ht := energyMultiplierSpline_on_cell j t hleft.le hright.le
  change
    energyMultiplierChi t = (r.chi:ℝ)+(r.cp:ℝ)*(t-a) ∧
    energyMultiplierF t = (r.f:ℝ)+(r.fp:ℝ)*(t-a) ∧
    energyMultiplierSigma t = (r.sigma:ℝ)+(r.sp:ℝ)*(t-a) at ht
  have hchiLoc : energyMultiplierChi =ᶠ[𝓝 t]
      fun s => energyMultiplierChi t+(r.cp:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have h := energyMultiplierSpline_on_cell j s hs.1.le hs.2.le
    change energyMultiplierChi s = (r.chi:ℝ)+(r.cp:ℝ)*(s-a) ∧
      energyMultiplierF s = (r.f:ℝ)+(r.fp:ℝ)*(s-a) ∧
      energyMultiplierSigma s = (r.sigma:ℝ)+(r.sp:ℝ)*(s-a) at h
    rw [h.1, ht.1]
    ring
  have hfLoc : energyMultiplierF =ᶠ[𝓝 t]
      fun s => energyMultiplierF t+(r.fp:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have h := energyMultiplierSpline_on_cell j s hs.1.le hs.2.le
    change energyMultiplierChi s = (r.chi:ℝ)+(r.cp:ℝ)*(s-a) ∧
      energyMultiplierF s = (r.f:ℝ)+(r.fp:ℝ)*(s-a) ∧
      energyMultiplierSigma s = (r.sigma:ℝ)+(r.sp:ℝ)*(s-a) at h
    rw [h.2.1, ht.2.1]
    ring
  have hsLoc : energyMultiplierSigma =ᶠ[𝓝 t]
      fun s => energyMultiplierSigma t+(r.sp:ℝ)*(s-t) := by
    filter_upwards [hnbd] with s hs
    have h := energyMultiplierSpline_on_cell j s hs.1.le hs.2.le
    change energyMultiplierChi s = (r.chi:ℝ)+(r.cp:ℝ)*(s-a) ∧
      energyMultiplierF s = (r.f:ℝ)+(r.fp:ℝ)*(s-a) ∧
      energyMultiplierSigma s = (r.sigma:ℝ)+(r.sp:ℝ)*(s-a) at h
    rw [h.2.2, ht.2.2]
    ring
  exact ⟨deriv_of_eventually_affine energyMultiplierChi t
      (energyMultiplierChi t) (r.cp:ℝ) hchiLoc,
    deriv_of_eventually_affine energyMultiplierF t
      (energyMultiplierF t) (r.fp:ℝ) hfLoc,
    deriv_of_eventually_affine energyMultiplierSigma t
      (energyMultiplierSigma t) (r.sp:ℝ) hsLoc⟩

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_derivs_on_open_cell
