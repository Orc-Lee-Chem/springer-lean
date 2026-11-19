import SpringerLean.Round1627EnergySplineTail

namespace SpringerLean

/-- The global continuous splines agree with the printed constant tail. -/
theorem energyMultiplierSpline_tail
    (t : ℝ) (ht : energyMultiplierKnotTime (21 : Fin 22) ≤ t) :
    energyMultiplierChi t = ((energyMultiplierEndpointRaw 42).chi:ℝ) ∧
    energyMultiplierF t = ((energyMultiplierEndpointRaw 42).f:ℝ) ∧
    energyMultiplierSigma t = ((energyMultiplierEndpointRaw 42).sigma:ℝ) := by
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
  have hchi := energyMultiplierSpline_generic_tail
    chiSlope chiNode hchiInc t ht
  have hf := energyMultiplierSpline_generic_tail
    fSlope fNode hfInc t ht
  have hs := energyMultiplierSpline_generic_tail
    sigmaSlope sigmaNode hsInc t ht
  have hzero : chiNode 0 = 0 ∧ fNode 0 = 0 ∧ sigmaNode 0 = 0 := by
    norm_num [chiNode, fNode, sigmaNode,
      energyMultiplierEndpointRaw, energyMultiplierNode]
  obtain ⟨hzc,hzf,hzs⟩ := hzero
  rw [hzc, sub_zero] at hchi
  rw [hzf, sub_zero] at hf
  rw [hzs, sub_zero] at hs
  exact ⟨hchi, hf, hs⟩

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_tail
