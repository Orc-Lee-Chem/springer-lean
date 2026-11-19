import SpringerLean.Round1718ActualFluxFieldAtZero
import SpringerLean.Round1635EnergySplineTailDerivatives

namespace SpringerLean

/-- A continuous real function with a constant tail is bounded for
nonnegative physical times. -/
theorem continuous_constant_tail_bounded
    (φ : ℝ → ℝ) (hφ : Continuous φ)
    (htail : ∀ t : ℝ, 1 ≤ t → φ t = φ 1) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |φ t| ≤ C := by
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max C0 |φ 1|, ?_⟩
  intro t ht0
  by_cases ht1 : t ≤ 1
  · have h := hC0 t ⟨ht0, ht1⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    rw [htail t ht1']
    exact le_max_right _ _

theorem energyMultipliers_bounded :
    (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |energyMultiplierChi t| ≤ C) ∧
    (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |energyMultiplierF t| ≤ C) ∧
    (∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |energyMultiplierSigma t| ≤ C) := by
  have htail (t : ℝ) (ht : 1 ≤ t) :
      energyMultiplierChi t = energyMultiplierChi 1 ∧
      energyMultiplierF t = energyMultiplierF 1 ∧
      energyMultiplierSigma t = energyMultiplierSigma 1 := by
    have ht' : energyMultiplierKnotTime (21 : Fin 22) ≤ t := by
      rw [energyMultiplierKnotTime_last]; exact ht
    have h1 : energyMultiplierKnotTime (21 : Fin 22) ≤ (1 : ℝ) := by
      rw [energyMultiplierKnotTime_last]
    have hv := energyMultiplierSpline_tail t ht'
    have hv1 := energyMultiplierSpline_tail 1 h1
    exact ⟨hv.1.trans hv1.1.symm,
      hv.2.1.trans hv1.2.1.symm,
      hv.2.2.trans hv1.2.2.symm⟩
  exact ⟨continuous_constant_tail_bounded energyMultiplierChi
      energyMultiplierChi_continuous (fun t ht => (htail t ht).1),
    continuous_constant_tail_bounded energyMultiplierF
      energyMultiplierF_continuous (fun t ht => (htail t ht).2.1),
    continuous_constant_tail_bounded energyMultiplierSigma
      energyMultiplierSigma_continuous (fun t ht => (htail t ht).2.2)⟩

end SpringerLean

#print axioms SpringerLean.continuous_constant_tail_bounded
#print axioms SpringerLean.energyMultipliers_bounded
