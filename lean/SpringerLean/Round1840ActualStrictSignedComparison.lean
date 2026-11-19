import SpringerLean.Round1839ActualTinyStrictComparison

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 1200000

/-- Every positive-deficit actual endpoint configuration has signed
cost strictly below the Catalan reference. All phase cases included. -/
theorem actualSignedPhaseIntegral_lt_two_reference
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) <
      2*comparisonPositiveDiskMoment (2*k-2) := by
  by_cases htiny : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) <
      (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ)))
  · exact actualSignedPhaseIntegral_tiny_first_strict F hc k hk beta hbeta ends htiny
  · have hcut₁ := le_of_not_gt htiny
    have hR := ends.first_max ends.P₂ (subset_convexHull ℝ (exteriorOmitted F) ends.mem₂)
    have hD : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) ≤ ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₂‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hcut₂ := hcut₁.trans hD
    have h₁ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₁ ends.θ₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ hcut₁
    have h₂ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₂ ends.θ₂
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂ hcut₂
    have hb := actualSignedPhaseIntegral_endpoint_phase_budget F hc k hk beta hbeta ends
    have hm0 : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2*k-2)
    have hN : 0 < ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) := by positivity
    have hcenter : 0 ≤ (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*(23/25 : ℝ)^(2*k-2) := by positivity
    apply lt_of_not_ge
    intro hcost
    have hnonneg := mul_nonneg hN.le (sub_nonneg.mpr hcost)
    dsimp only at hb
    linarith

theorem exteriorInverseCoeff_candidate_nonslit_false
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) : False := by
  obtain ⟨beta,hbeta,⟨ends⟩,hcost⟩ := exteriorInverseCoeff_candidate_exists_signed_phase_data F hc k hk hB hns
  exact (not_lt_of_ge hcost) (actualSignedPhaseIntegral_lt_two_reference F hc k hk beta hbeta ends)

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_lt_two_reference
#print axioms SpringerLean.exteriorInverseCoeff_candidate_nonslit_false
