import SpringerLean.Round1774ActualCandidatePhaseEndpoints
import SpringerLean.Round1773ActualSignedPhaseIntegral
import SpringerLean.Round1775ComparisonPositiveCatalan

open MeasureTheory Metric

namespace SpringerLean

/-- The exact signed comparison criterion and the SAME actual endpoint
data now share the coefficient-selected phase. The candidate includes
equality and the reference is the actual positive-part disk integral. -/
theorem exteriorInverseCoeff_candidate_exists_signed_phase_data
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ Nonempty (ActualCandidatePhaseEndpoints F k beta) ∧
      2*comparisonPositiveDiskMoment (2*k-2) ≤
        Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) := by
  obtain ⟨beta, hbeta, hcost⟩ :=
    exteriorInverseCoeff_candidate_exists_signed_phase_integral F hc k hk hB
  have hends := exteriorInverseCoeff_candidate_phase_endpoints_nonempty F hc k hk hB hns beta hbeta
  have href := comparisonPositiveDiskMoment_catalan (by omega : 2 ≤ k)
  rw [pow_succ] at href
  have hpow : 0 < (2 : ℝ)^(2*k-2) := by positivity
  have hratio : (catalan (k-1) : ℝ)/(2 : ℝ)^(2*k-2)=
      2*comparisonPositiveDiskMoment (2*k-2) := by
    apply (div_eq_iff hpow.ne').mpr
    nlinarith [href]
  rw [hratio] at hcost
  exact ⟨beta, hbeta, hends, hcost⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_exists_signed_phase_data
