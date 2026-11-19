import SpringerLean.Round1838TinyCentralScalar
import SpringerLean.Round1836ActualAntipodalIntegral

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 1300000

theorem actualSignedPhaseIntegral_endpoint_phase_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    let m := ((2*k-2 : ℕ) : ℝ)
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z)-
      2*comparisonPositiveDiskMoment (2*k-2)) ≤
      endpointPhaseBudget k ends.P₁ ends.θ₁+endpointPhaseBudget k ends.P₂ ends.θ₂+
        m*Real.sqrt m*(23/25 : ℝ)^(2*k-2) := by
  obtain ⟨hP₁,hP₂⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have h₁ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₁ ends.v₁ ends.θ₁ ends.unit₁ hP₁ ends.saving₁
  have h₂ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₂ ends.v₂ ends.θ₂ ends.unit₂ hP₂ ends.saving₂
  have hi := actualSignedPhaseIntegral_endpointTests_le F hc k hk beta hbeta ends
  have hh := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) by positivity)
  dsimp only
  nlinarith [hh,h₁,h₂]

theorem actualSignedPhaseIntegral_tiny_first_strict
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (htiny : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) <
      (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ)))) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) <
      2*comparisonPositiveDiskMoment (2*k-2) := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let d := 2-‖ends.P₁‖
  have hm : (1500 : ℝ) ≤ m := by dsimp [m,mn]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hd : 0 < d := ends.deficit_pos₁
  have hX : 0 < Real.log (100*m) := Real.log_pos (by nlinarith)
  have hsmall : d ≤ (3/100 : ℝ)/(m^2*Real.log (100*m)) := by
    change m*d < (3/100 : ℝ)/(m*Real.log (100*m)) at htiny
    apply (le_div_iff₀ (by positivity : 0 < m^2*Real.log (100*m))).mpr
    have hh := (lt_div_iff₀ (mul_pos hm0 hX)).mp htiny
    nlinarith
  have hL := (endpointPhaseParameter_scalar_relations k hk ends.P₁ ends.deficit_pos₁ ends.scaled_deficit₁).1
  have hs := tiny_central_cost_lt_cubic k hk hd hL.le hsmall
  have hb := actualSignedPhaseIntegral_antipodal_budget F hc k hk beta hbeta ends
  have hN : 0 < m*Real.sqrt m := by positivity
  apply lt_of_not_ge
  intro hcost
  have hnonneg := mul_nonneg hN.le (sub_nonneg.mpr hcost)
  dsimp only at hs hb
  change 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ)*
    (Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z)-
      2*comparisonPositiveDiskMoment (2*k-2)) at hnonneg
  nlinarith [hs,hb,hnonneg]

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_tiny_first_strict
