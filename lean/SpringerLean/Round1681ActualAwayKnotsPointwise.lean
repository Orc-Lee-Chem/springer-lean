import SpringerLean.Round1680ActualTailEnergyPointwise
import SpringerLean.Round1675ActualCellEnergyPointwise

namespace SpringerLean
noncomputable section

/-- The actual C=25/16 pointwise inequality at every regular filling
point whose physical multiplier time is away from the finite knots. -/
theorem actualHarmonicPhase_pointwise_away_knots
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hnotKnot : ∀ j : Fin 22,
      actualHarmonicMultiplierTime F k z ≠ energyMultiplierKnotTime j) :
    let U := actualHarmonicPhaseField F k beta
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    let u := U z/‖actualHarmonic F z‖
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    (k:ℝ)^2*u^2+b*actualEnergyFluxDiv F k beta z ≤
      (25/16)*p^2 := by
  let t := actualHarmonicMultiplierTime F k z
  have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
  rcases energyMultiplier_time_covered t ht with hcell | htail
  · obtain ⟨i, hleft0, hright0⟩ := hcell
    have htimes := energyMultiplier_cell_endpoint_times i
    have hleft : energyMultiplierKnotTime i.castSucc < t := by
      have hl : energyMultiplierKnotTime i.castSucc ≤ t := by
        rw [← htimes.1]
        exact hleft0
      rcases eq_or_lt_of_le hl with heq | hlt
      · exact False.elim ((hnotKnot i.castSucc) heq.symm)
      · exact hlt
    have hright : t < energyMultiplierKnotTime i.succ := by
      have hr : t ≤ energyMultiplierKnotTime i.succ := by
        rw [← htimes.2]
        exact hright0
      rcases eq_or_lt_of_le hr with heq | hlt
      · exact False.elim ((hnotKnot i.succ) heq)
      · exact hlt
    exact actualHarmonicPhase_pointwise_cell
      F hc k hk beta hbeta i hz hz0 hH hleft hright
  · have htail' : 1 < t := by
      have hlast : ((energyMultiplierEndpointRaw 42).t:ℝ) = 1 := by
        norm_num [energyMultiplierEndpointRaw, energyMultiplierNode]
      have hl : 1 ≤ t := by simpa [hlast] using htail
      rcases eq_or_lt_of_le hl with heq | hlt
      · exact False.elim ((hnotKnot (21 : Fin 22))
          (by simpa [energyMultiplierKnotTime_last] using heq.symm))
      · exact hlt
    exact actualHarmonicPhase_pointwise_tail
      F hc k hk beta hbeta hz hz0 hH htail'

end
end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_pointwise_away_knots
