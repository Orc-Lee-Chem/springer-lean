import SpringerLean.Round1812ActualTrueAxisIntegralCost

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 1000000

def endpointPhaseBudget (k : ℕ) (P : ℂ) (δ : ℝ) : ℝ :=
  let m := ((2*k-2 : ℕ) : ℝ)
  let N := m*Real.sqrt m
  if |(k : ℝ)*δ| ≤ Real.pi/3 then
    N*(alignedPhaseReferenceCost k (endpointPhaseParameter k P)-
      comparisonPositiveDiskMoment (2*k-2))-(m*(2-‖P‖))^3/32
  else -N*comparisonPositiveDiskMoment (2*k-2)/m

theorem endpointPhaseTest_actual_integral_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P v : ℂ) (δ : ℝ) (hv : ‖v‖=1) (hP : 0 < ‖P‖)
    (hgain : ∀ R : ℝ, 0 ≤ R →
      ((((2*k-2 : ℕ) : ℝ)*(2-‖P‖))^3/32 < actualTwoPowerSaving F (2*k-12) R v)) :
    (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
      (Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, endpointPhaseTest k P v δ (actualHarmonic F z))-
        comparisonPositiveDiskMoment (2*k-2)) ≤ endpointPhaseBudget k P δ := by
  have hm : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2*k-2)
  have hN : 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) := by positivity
  unfold endpointPhaseTest endpointPhaseBudget
  dsimp only
  by_cases halign : |(k : ℝ)*δ| ≤ Real.pi/3
  · simp only [if_pos halign]
    have hau : endpointPhaseParameter k P ≤ ((2*k-2 : ℕ) : ℝ)/5 := min_le_right _ _
    have hR : 0 ≤ 2*(1-endpointPhaseParameter k P/((2*k-2 : ℕ) : ℝ)) := by
      have hh : endpointPhaseParameter k P/((2*k-2 : ℕ) : ℝ) ≤ 1 :=
        (div_le_one hm).mpr (by linarith)
      linarith
    have hs := hgain _ hR
    rw [←alignedPhaseTest_saving_identity F hc k hk (endpointPhaseParameter k P) v hv] at hs
    linarith
  · simp only [if_neg halign]
    have haxis : ‖P/(‖P‖ : ℂ)‖=1 := by
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,div_self hP.ne']
    have hh := actualHarmonic_trueAxis_integral_le F hc k hk _ haxis
    calc
      _ ≤ (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*
          ((1-1/((2*k-2 : ℕ) : ℝ))*comparisonPositiveDiskMoment (2*k-2)-
            comparisonPositiveDiskMoment (2*k-2)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hh _) hN
      _ = _ := by ring

/-- Every actual candidate phase is now reduced to a single explicit
scalar budget. This is a necessary condition, not the exclusion yet. -/
theorem exteriorInverseCoeff_candidate_necessary_pure_phase_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ ∃ ends : ActualCandidatePhaseEndpoints F k beta,
      0 ≤ endpointPhaseBudget k ends.P₁ ends.θ₁+endpointPhaseBudget k ends.P₂ ends.θ₂+
        (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*(23/25 : ℝ)^(2*k-2) := by
  obtain ⟨beta,hbeta,⟨ends⟩,hcost⟩ := exteriorInverseCoeff_candidate_exists_signed_phase_data F hc k hk hB hns
  refine ⟨beta,hbeta,ends,?_⟩
  obtain ⟨hP₁,hP₂⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have h₁ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₁ ends.v₁ ends.θ₁ ends.unit₁ hP₁ ends.saving₁
  have h₂ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₂ ends.v₂ ends.θ₂ ends.unit₂ hP₂ ends.saving₂
  have hi := actualSignedPhaseIntegral_endpointTests_le F hc k hk beta hbeta ends
  have hh := hcost.trans hi
  have hN : 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) := by positivity
  have hn := mul_le_mul_of_nonneg_left hh hN
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.endpointPhaseTest_actual_integral_budget
#print axioms SpringerLean.exteriorInverseCoeff_candidate_necessary_pure_phase_budget
