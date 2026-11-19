import SpringerLean.Round1792SelectedOuterPhaseProjections
import SpringerLean.Round1789ActualAlignedTwoPowerCost

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 600000

def alignedPhaseTest (k : ℕ) (a : ℝ) (v w : ℂ) : ℝ :=
  twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12) ((conj v*w).re)/
    (2 : ℝ)^(2*k-2)

theorem alignedPhaseTest_nonneg (k : ℕ) (a : ℝ) (v w : ℂ) :
    0 ≤ alignedPhaseTest k a v w := by
  unfold alignedPhaseTest twoPowerPhaseTest
  apply div_nonneg _ (by positivity)
  exact (pow_nonneg (le_max_right _ _) _).trans (le_max_left _ _)

theorem actualSignedPhaseDensity_two_aligned_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3)
    (hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3)
    (a₁ a₂ : ℝ) (ha₁ : 6 ≤ a₁) (ha₂ : 6 ≤ a₂)
    (hay₁ : a₁*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₁) ≤ 3)
    (hay₂ : a₂*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₂) ≤ 3)
    (z : ℂ) (hz : ‖z‖ < 1) (hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖) :
    actualSignedPhaseDensity F k beta z ≤
      alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z)+
        alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z) := by
  have hproj := ActualCandidatePhaseEndpoints.outer_projections F hc k hk beta ends
  have hmem := actualHarmonic_mem_convexHull_omitted F hc hz
  have hnonneg₁ := alignedPhaseTest_nonneg k a₁ ends.v₁ (actualHarmonic F z)
  have hnonneg₂ := alignedPhaseTest_nonneg k a₂ ends.v₂ (actualHarmonic F z)
  by_cases hforward : 0 ≤ (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*actualHarmonic F z).re
  · have hx := hproj.1 _ hmem hr hforward
    have hh := actualSignedPhaseDensity_aligned_le_twoPower F hc k hk ends.P₁ ends.mem₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.scaled_width₁ beta ends.v₁ ends.unit₁
      ends.phase₁ ends.θ₁ ends.ray₁ hδ₁ z hz hx.le a₁ ha₁ hay₁
    change actualSignedPhaseDensity F k beta z ≤ alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z) at hh
    linarith
  · have hback := le_of_lt (lt_of_not_ge hforward)
    have hx := hproj.2 _ hmem hr hback
    have hh := actualSignedPhaseDensity_aligned_le_twoPower F hc k hk ends.P₂ ends.mem₂
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.scaled_width₂ beta ends.v₂ ends.unit₂
      ends.phase₂ ends.θ₂ ends.ray₂ hδ₂ z hz hx.le a₂ ha₂ hay₂
    change actualSignedPhaseDensity F k beta z ≤ alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z) at hh
    linarith

theorem actualSignedPhaseDensity_two_aligned_global
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3)
    (hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3)
    (a₁ a₂ : ℝ) (ha₁ : 6 ≤ a₁) (ha₂ : 6 ≤ a₂)
    (hay₁ : a₁*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₁) ≤ 3)
    (hay₂ : a₂*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₂) ≤ 3)
    (z : ℂ) (hz : ‖z‖ < 1) :
    actualSignedPhaseDensity F k beta z ≤
      alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z)+
        alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2) := by
  by_cases hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖
  · have hh := actualSignedPhaseDensity_two_aligned_outer F hc k hk beta ends hδ₁ hδ₂
      a₁ a₂ ha₁ ha₂ hay₁ hay₂ z hz hr
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
    have hnonneg₁ := alignedPhaseTest_nonneg k a₁ ends.v₁ (actualHarmonic F z)
    have hnonneg₂ := alignedPhaseTest_nonneg k a₂ ends.v₂ (actualHarmonic F z)
    linarith

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_two_aligned_global
