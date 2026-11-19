import SpringerLean.Round1799ActualFixedAlignedBudget
import SpringerLean.Round1776ActualCandidateSignedPhaseData

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 800000

/-- A weak nonslit Catalan candidate either uses a nonaligned endpoint
or violates the desired pure reference-cost budget. All actual-map
energy, projection, parameter and saving premises are discharged. -/
theorem exteriorInverseCoeff_candidate_phase_reference_alternative
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ ∃ ends : ActualCandidatePhaseEndpoints F k beta,
      Real.pi/3 < |(k : ℝ)*ends.θ₁| ∨ Real.pi/3 < |(k : ℝ)*ends.θ₂| ∨
      let m := ((2*k-2 : ℕ) : ℝ)
      let D₁ := m*(2-‖ends.P₁‖)
      let D₂ := m*(2-‖ends.P₂‖)
      let a₁ := endpointPhaseParameter k ends.P₁
      let a₂ := endpointPhaseParameter k ends.P₂
      (D₁^3+D₂^3)/32 <
        m*Real.sqrt m*((alignedPhaseReferenceCost k a₁-comparisonPositiveDiskMoment (2*k-2))+
          (alignedPhaseReferenceCost k a₂-comparisonPositiveDiskMoment (2*k-2))+
          (23/25 : ℝ)^(2*k-2)) := by
  obtain ⟨beta, hbeta, ⟨ends⟩, hcost⟩ :=
    exteriorInverseCoeff_candidate_exists_signed_phase_data F hc k hk hB hns
  refine ⟨beta,hbeta,ends,?_⟩
  by_cases hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3
  · by_cases hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3
    · right; right
      have hb := actualSignedPhaseIntegral_two_aligned_fixed_budget F hc k hk beta hbeta ends hδ₁ hδ₂
      have hnonneg : 0 ≤ (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
          (Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z)-
            2*comparisonPositiveDiskMoment (2*k-2)) := by
        exact mul_nonneg (by positivity) (sub_nonneg.mpr hcost)
      dsimp only at hb ⊢
      nlinarith
    · exact Or.inr (Or.inl (lt_of_not_ge hδ₂))
  · exact Or.inl (lt_of_not_ge hδ₁)

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_phase_reference_alternative
