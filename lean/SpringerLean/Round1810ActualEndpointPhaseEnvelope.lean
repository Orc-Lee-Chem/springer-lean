import SpringerLean.Round1807ActualTrueAxisPhaseCost
import SpringerLean.Round1800CandidateReferenceBudget

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 1100000

def endpointPhaseTest (k : ℕ) (P v : ℂ) (δ : ℝ) (w : ℂ) : ℝ :=
  if |(k : ℝ)*δ| ≤ Real.pi/3 then
    alignedPhaseTest k (endpointPhaseParameter k P) v w
  else trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*
    (max ((conj (P/(‖P‖ : ℂ))*w).re/2) 0)^(2*k-10)

theorem endpointPhaseTest_nonneg (k : ℕ) (hk : 751 ≤ k)
    (P v : ℂ) (δ : ℝ) (w : ℂ) : 0 ≤ endpointPhaseTest k P v δ w := by
  unfold endpointPhaseTest
  split_ifs
  · exact alignedPhaseTest_nonneg _ _ _ _
  · have hm : (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1500 ≤ 2*k-2)
    exact mul_nonneg (trueAxisMomentRatioLambda_pos_and_log hm).1.le (pow_nonneg (le_max_right _ _) _)

theorem actualSignedPhaseDensity_le_endpointPhaseTest
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hlog : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2)
    (hwidth : exteriorFineEndpointWidth P < (1/3 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)))
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |δ| ≤ Real.pi/(2*(k : ℝ)))
    (z : ℂ) (hz : ‖z‖ < 1)
    (hxray : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (hxaxis : (9/5 : ℝ) ≤ (conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re) :
    actualSignedPhaseDensity F k beta z ≤ endpointPhaseTest k P v δ (actualHarmonic F z) := by
  unfold endpointPhaseTest
  by_cases halign : |(k : ℝ)*δ| ≤ Real.pi/3
  · rw [if_pos halign]
    obtain ⟨_,_,ha,_,hay⟩ := endpointPhaseParameter_bounds k hk P hd ht hlog hwidth
    exact actualSignedPhaseDensity_aligned_le_twoPower F hc k hk P hP hd ht hW beta v hvunit
      hphase δ hv halign z hz hxray (endpointPhaseParameter k P) ha hay
  · rw [if_neg halign]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hupper : |(k : ℝ)*δ| ≤ Real.pi/2 := by
      rw [abs_mul,abs_of_pos hk0]
      have hh := (le_div_iff₀ (show (0 : ℝ) < 2*(k : ℝ) by positivity)).mp hδ
      nlinarith
    exact (actualSignedPhaseDensity_trueAxis_lt_lower_power F hc k hk P hP hd ht hW beta v
      hphase δ hv (le_of_lt (lt_of_not_ge halign)) hupper z hz hxaxis).le

theorem ActualCandidatePhaseEndpoints.outer_axis_projections
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    (∀ w ∈ convexHull ℝ (exteriorOmitted F), (46/25 : ℝ) ≤ ‖w‖ →
      0 ≤ (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*w).re →
      (9/5 : ℝ) < (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*w).re) ∧
    (∀ w ∈ convexHull ℝ (exteriorOmitted F), (46/25 : ℝ) ≤ ‖w‖ →
      (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*w).re ≤ 0 →
      (9/5 : ℝ) < (conj (ends.P₂/(‖ends.P₂‖ : ℂ))*w).re) := by
  constructor
  · intro w hw hr hforward
    exact exteriorOmitted_actualEndpoint_forward_outer_projection F hc k hk ends.P₁ ends.mem₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.scaled_width₁ w hw hr hforward
      (ends.P₁/(‖ends.P₁‖ : ℂ)) (by norm_num)
  · intro w hw hr hback
    exact exteriorOmitted_selected_second_outer_projection F hc k hk ends.P₁ ends.P₂
      ends.mem₁ ends.mem₂ ends.deficit_pos₁ ends.scaled_deficit₁ ends.scaled_width₁
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.opposite w hw hr hback
      (ends.P₂/(‖ends.P₂‖ : ℂ)) (by norm_num)

theorem actualSignedPhaseDensity_endpointTests_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) (hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖) :
    actualSignedPhaseDensity F k beta z ≤
      endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z) := by
  have hproj := ActualCandidatePhaseEndpoints.outer_projections F hc k hk beta ends
  have haxis := ActualCandidatePhaseEndpoints.outer_axis_projections F hc k hk beta ends
  have hmem := actualHarmonic_mem_convexHull_omitted F hc hz
  have hnonneg₁ := endpointPhaseTest_nonneg k hk ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)
  have hnonneg₂ := endpointPhaseTest_nonneg k hk ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)
  by_cases hforward : 0 ≤ (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*actualHarmonic F z).re
  · have hh := actualSignedPhaseDensity_le_endpointPhaseTest F hc k hk ends.P₁ ends.mem₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ ends.scaled_width₁
      beta ends.v₁ ends.unit₁ ends.phase₁ ends.θ₁ ends.ray₁ ends.angle₁ z hz
      (hproj.1 _ hmem hr hforward).le (haxis.1 _ hmem hr hforward).le
    linarith
  · have hback := le_of_lt (lt_of_not_ge hforward)
    have hh := actualSignedPhaseDensity_le_endpointPhaseTest F hc k hk ends.P₂ ends.mem₂
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂ ends.scaled_width₂
      beta ends.v₂ ends.unit₂ ends.phase₂ ends.θ₂ ends.ray₂ ends.angle₂ z hz
      (hproj.2 _ hmem hr hback).le (haxis.2 _ hmem hr hback).le
    linarith

theorem actualSignedPhaseDensity_endpointTests_global
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) :
    actualSignedPhaseDensity F k beta z ≤
      endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2) := by
  by_cases hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖
  · have hh := actualSignedPhaseDensity_endpointTests_outer F hc k hk beta ends z hz hr
    linarith [show 0 ≤ (23/25 : ℝ)^(2*k-2) by positivity]
  · have hfrac : ‖actualHarmonic F z‖/2 ≤ (23/25 : ℝ) := by linarith
    have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ ‖actualHarmonic F z‖/2) hfrac (2*k-2)
    rw [div_pow] at hpower
    have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
      unfold actualHarmonicPhasePotentialDensity
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hraw : ‖actualHarmonic F z‖^(2*k-2)-(8/25 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤
        ‖actualHarmonic F z‖^(2*k-2) := by nlinarith
    have hsigned := div_le_div_of_nonneg_right hraw (by positivity : 0 ≤ (2 : ℝ)^(2*k-2))
    change actualSignedPhaseDensity F k beta z ≤ _ at hsigned
    have hnonneg₁ := endpointPhaseTest_nonneg k hk ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)
    have hnonneg₂ := endpointPhaseTest_nonneg k hk ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)
    linarith

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_endpointTests_global
