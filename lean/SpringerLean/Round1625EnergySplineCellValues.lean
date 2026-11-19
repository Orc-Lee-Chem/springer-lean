import SpringerLean.Round1624EnergySplineGenericCell

namespace SpringerLean

/-- The three explicit continuous splines are exactly the original
printed affine profile throughout each closed finite cell. -/
theorem energyMultiplierSpline_on_cell
    (j : Fin 21) (t : ℝ)
    (hleft : energyMultiplierKnotTime j.castSucc ≤ t)
    (hright : t ≤ energyMultiplierKnotTime j.succ) :
    let r := energyMultiplierEndpointRaw (2*j.val)
    energyMultiplierChi t = (r.chi:ℝ) + (r.cp:ℝ)*
      (t-energyMultiplierKnotTime j.castSucc) ∧
    energyMultiplierF t = (r.f:ℝ) + (r.fp:ℝ)*
      (t-energyMultiplierKnotTime j.castSucc) ∧
    energyMultiplierSigma t = (r.sigma:ℝ) + (r.sp:ℝ)*
      (t-energyMultiplierKnotTime j.castSucc) := by
  let chiNode : ℕ → ℝ := fun i => (energyMultiplierEndpointRaw (2*i)).chi
  let fNode : ℕ → ℝ := fun i => (energyMultiplierEndpointRaw (2*i)).f
  let sigmaNode : ℕ → ℝ := fun i => (energyMultiplierEndpointRaw (2*i)).sigma
  let chiSlope : Fin 21 → ℝ := fun i => (energyMultiplierEndpointRaw (2*i.val)).cp
  let fSlope : Fin 21 → ℝ := fun i => (energyMultiplierEndpointRaw (2*i.val)).fp
  let sigmaSlope : Fin 21 → ℝ := fun i => (energyMultiplierEndpointRaw (2*i.val)).sp
  have hchiInc : ∀ i : Fin 21,
      chiSlope i*(energyMultiplierKnotTime i.succ-
        energyMultiplierKnotTime i.castSucc) =
        chiNode (i.val+1)-chiNode i.val := by
    intro i
    exact (energyMultiplier_cell_increments i).1
  have hfInc : ∀ i : Fin 21,
      fSlope i*(energyMultiplierKnotTime i.succ-
        energyMultiplierKnotTime i.castSucc) =
        fNode (i.val+1)-fNode i.val := by
    intro i
    exact (energyMultiplier_cell_increments i).2.1
  have hsInc : ∀ i : Fin 21,
      sigmaSlope i*(energyMultiplierKnotTime i.succ-
        energyMultiplierKnotTime i.castSucc) =
        sigmaNode (i.val+1)-sigmaNode i.val := by
    intro i
    exact (energyMultiplier_cell_increments i).2.2
  have hchi := energyMultiplierSpline_generic_on_cell
    chiSlope chiNode hchiInc j t hleft hright
  have hf := energyMultiplierSpline_generic_on_cell
    fSlope fNode hfInc j t hleft hright
  have hs := energyMultiplierSpline_generic_on_cell
    sigmaSlope sigmaNode hsInc j t hleft hright
  have hzero : chiNode 0 = 0 ∧ fNode 0 = 0 ∧ sigmaNode 0 = 0 := by
    norm_num [chiNode, fNode, sigmaNode,
      energyMultiplierEndpointRaw, energyMultiplierNode]
  obtain ⟨hzc,hzf,hzs⟩ := hzero
  rw [hzc, sub_zero] at hchi
  rw [hzf, sub_zero] at hf
  rw [hzs, sub_zero] at hs
  exact ⟨hchi, hf, hs⟩

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_on_cell
