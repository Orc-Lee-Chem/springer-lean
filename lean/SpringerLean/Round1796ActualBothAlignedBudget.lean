import SpringerLean.Round1795ActualAlignedSavingIdentity

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 700000

/-- Actual two-aligned disk budget in the SAME m^(3/2) normalization
as the cubic endpoint savings. Only the pure reference excess costs
and the central allowance remain on the right. -/
theorem actualSignedPhaseIntegral_two_aligned_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3)
    (hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3)
    (a₁ a₂ : ℝ) (ha₁ : 6 ≤ a₁) (ha₂ : 6 ≤ a₂)
    (hau₁ : a₁ ≤ ((2*k-2 : ℕ) : ℝ)/5)
    (hau₂ : a₂ ≤ ((2*k-2 : ℕ) : ℝ)/5)
    (hay₁ : a₁*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₁) ≤ 3)
    (hay₂ : a₂*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₂) ≤ 3) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let D₁ := m*(2-‖ends.P₁‖)
    let D₂ := m*(2-‖ends.P₂‖)
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
      actualSignedPhaseDensity F k beta z)-2*comparisonPositiveDiskMoment (2*k-2)) <
    m*Real.sqrt m*((alignedPhaseReferenceCost k a₁-comparisonPositiveDiskMoment (2*k-2))+
      (alignedPhaseReferenceCost k a₂-comparisonPositiveDiskMoment (2*k-2))+
      (23/25 : ℝ)^(2*k-2))-(D₁^3+D₂^3)/32 := by
  have hi := actualSignedPhaseIntegral_two_aligned_le F hc k hk beta hbeta ends
    hδ₁ hδ₂ a₁ a₂ ha₁ ha₂ hay₁ hay₂
  obtain ⟨hs₁, hs₂⟩ := ActualCandidatePhaseEndpoints.aligned_integral_savings
    F hc k hk beta ends a₁ a₂ hau₁ hau₂
  have hm : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2*k-2)
  have hnorm : 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) := by positivity
  have hip := mul_le_mul_of_nonneg_left hi hnorm
  dsimp
  nlinarith [hip, hs₁, hs₂]

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_two_aligned_budget
