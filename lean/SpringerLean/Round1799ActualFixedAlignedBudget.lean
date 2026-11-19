import SpringerLean.Round1796ActualBothAlignedBudget
import SpringerLean.Round1797ActualPhaseParameters

open MeasureTheory Metric

namespace SpringerLean

/-- Both crossover parameters are now the fixed paper choices derived
from the actual endpoints, with no remaining admissibility premises. -/
theorem actualSignedPhaseIntegral_two_aligned_fixed_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3)
    (hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let D₁ := m*(2-‖ends.P₁‖)
    let D₂ := m*(2-‖ends.P₂‖)
    let a₁ := endpointPhaseParameter k ends.P₁
    let a₂ := endpointPhaseParameter k ends.P₂
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
      actualSignedPhaseDensity F k beta z)-2*comparisonPositiveDiskMoment (2*k-2)) <
    m*Real.sqrt m*((alignedPhaseReferenceCost k a₁-comparisonPositiveDiskMoment (2*k-2))+
      (alignedPhaseReferenceCost k a₂-comparisonPositiveDiskMoment (2*k-2))+
      (23/25 : ℝ)^(2*k-2))-(D₁^3+D₂^3)/32 := by
  obtain ⟨_,_,ha₁,hu₁,hay₁⟩ := endpointPhaseParameter_bounds k hk ends.P₁
    ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁
  obtain ⟨_,_,ha₂,hu₂,hay₂⟩ := endpointPhaseParameter_bounds k hk ends.P₂
    ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂
  exact actualSignedPhaseIntegral_two_aligned_budget F hc k hk beta hbeta ends hδ₁ hδ₂
    (endpointPhaseParameter k ends.P₁) (endpointPhaseParameter k ends.P₂)
    ha₁ ha₂ hu₁ hu₂ hay₁ hay₂

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_two_aligned_fixed_budget
