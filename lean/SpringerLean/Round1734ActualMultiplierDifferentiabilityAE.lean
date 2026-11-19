import SpringerLean.Round1733CartesianDivergenceLinear
import SpringerLean.Round1636ActualSplineCompositions
import SpringerLean.Round1701ActualKnotMultiplierHasFDerivAE

open MeasureTheory

namespace SpringerLean

/-- On one full-measure set of regular source points, all three actual
multiplier compositions are differentiable. The knot levels are kept:
there the derivative is zero, even if the level has positive area. -/
theorem actualEnergyMultiplier_compositions_differentiableAt_regular_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      DifferentiableAt ℝ (fun w => energyMultiplierChi
        (actualHarmonicMultiplierTime F k w)) z ∧
      DifferentiableAt ℝ (fun w => energyMultiplierF
        (actualHarmonicMultiplierTime F k w)) z ∧
      DifferentiableAt ℝ (fun w => energyMultiplierSigma
        (actualHarmonicMultiplierTime F k w)) z := by
  filter_upwards
    [actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k]
    with z hknot hreg
  obtain ⟨hball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let t := actualHarmonicMultiplierTime F k z
  by_cases hnot : ∀ j : Fin 22,
      t ≠ energyMultiplierKnotTime j
  · have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hball
    rcases energyMultiplier_time_covered t ht with hcell | htail
    · obtain ⟨i, hleft0, hright0⟩ := hcell
      have htimes := energyMultiplier_cell_endpoint_times i
      have hleft : energyMultiplierKnotTime i.castSucc < t := by
        have hl : energyMultiplierKnotTime i.castSucc ≤ t := by
          rw [← htimes.1]
          exact hleft0
        rcases eq_or_lt_of_le hl with heq | hlt
        · exact False.elim ((hnot i.castSucc) heq.symm)
        · exact hlt
      have hright : t < energyMultiplierKnotTime i.succ := by
        have hr : t ≤ energyMultiplierKnotTime i.succ := by
          rw [← htimes.2]
          exact hright0
        rcases eq_or_lt_of_le hr with heq | hlt
        · exact False.elim ((hnot i.succ) heq)
        · exact hlt
      exact actualEnergyMultiplier_compositions_differentiableAt_cell
        F hc k i hball hz0 hH hleft hright
    · have htail' : 1 < t := by
        have hlast : ((energyMultiplierEndpointRaw 42).t : ℝ) = 1 := by
          norm_num [energyMultiplierEndpointRaw, energyMultiplierNode]
        have hl : 1 ≤ t := by simpa [hlast] using htail
        rcases eq_or_lt_of_le hl with heq | hlt
        · exact False.elim ((hnot (21 : Fin 22))
            (by simpa [energyMultiplierKnotTime_last] using heq.symm))
        · exact hlt
      exact actualEnergyMultiplier_compositions_differentiableAt_tail
        F hc k hball hz0 hH htail'
  · push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    obtain ⟨hchi, hf, hs⟩ := hknot i hreg hi
    exact ⟨hchi.differentiableAt, hf.differentiableAt,
      hs.differentiableAt⟩

end SpringerLean

#print axioms SpringerLean.actualEnergyMultiplier_compositions_differentiableAt_regular_ae
