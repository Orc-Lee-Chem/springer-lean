import SpringerLean.Round1829ActualNonTinyPhaseBudget

namespace SpringerLean
set_option maxHeartbeats 900000

/-- All ordinary-size positive deficits are excluded on the actual
function. Only the joint tiny-deficit comparison remains. -/
theorem exteriorInverseCoeff_candidate_has_tiny_endpoint
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ ∃ ends : ActualCandidatePhaseEndpoints F k beta,
      let m := ((2*k-2 : ℕ) : ℝ)
      m*(2-‖ends.P₁‖) < (3/100 : ℝ)/(m*Real.log (100*m)) ∨
      m*(2-‖ends.P₂‖) < (3/100 : ℝ)/(m*Real.log (100*m)) := by
  obtain ⟨beta,hbeta,ends,hbudget⟩ := exteriorInverseCoeff_candidate_necessary_pure_phase_budget F hc k hk hB hns
  refine ⟨beta,hbeta,ends,?_⟩
  dsimp only
  by_contra hnone
  have hcut₁ : (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ))) ≤
      ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) := by push_neg at hnone; exact hnone.1
  have hcut₂ : (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ))) ≤
      ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₂‖) := by push_neg at hnone; exact hnone.2
  have h₁ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₁ ends.θ₁
    ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ hcut₁
  have h₂ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₂ ends.θ₂
    ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂ hcut₂
  have hcenter : 0 ≤ (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*(23/25 : ℝ)^(2*k-2) := by positivity
  linarith

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_has_tiny_endpoint
