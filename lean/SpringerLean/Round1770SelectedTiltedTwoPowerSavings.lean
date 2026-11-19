import SpringerLean.Round1769ActualTwoPowerRetention

open Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 500000

theorem actualHarmonic_twoPower_cubic_gain_thirtysecond
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ℂ) (hv : ‖v‖=1) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 < D)
    {j : ℕ} (hj : 1490 ≤ j)
    (hgain : D^3/30 < actualDirectionalPowerSaving F (j+10) v) :
    D^3/32 < actualTwoPowerSaving F j R v := by
  have hκ := phasePowerRetention_ge_fortynine_fiftieths hj
  have hD3 : 0 < D^3 := by positivity
  have hs := actualHarmonic_twoPower_cubic_gain_of_directional F hc v hv hR j hgain
  have hh := mul_le_mul_of_nonneg_right hκ hD3.le
  nlinarith

/-- The actual candidate supplies one pair for ALL crossover parameters
and the required tilted rays. Both endpoint selections and the fine
width data survive; the two-power saving is strictly >D_i^3/32. -/
theorem exteriorInverseCoeff_candidate_selected_two_tilted_twoPower_savings
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖) < 3/20 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) < 3/2 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) < 3/2 ∧
      exteriorFineEndpointWidth P₁ < (1/3 : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) ∧
      exteriorFineEndpointWidth P₂ < (1/3 : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) ∧
      ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₁ < 1/2 ∧
      ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₂ < 1/2 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      (∀ (R : ℝ), 0 ≤ R → ∀ v : ℂ, ‖v‖=1 →
        ((((2*k-2 : ℕ) : ℝ)*(2-‖P₁‖))^3/32 <
          actualTwoPowerSaving F (2*k-12) R v)) ∧
      (∀ (R : ℝ), 0 ≤ R → ∀ v : ℂ, ‖v‖=1 →
        ‖v-P₂/(‖P₂‖ : ℂ)‖ ≤ 1/4 →
        ((((2*k-2 : ℕ) : ℝ)*(2-‖P₂‖))^3/32 <
          actualTwoPowerSaving F (2*k-12) R v)) := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hd₁, hd₂, ht₁, ht₂, hlog₁, hlog₂,
    hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂, hsave₁, hsave₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_tilted_disk_savings F hc k hk hB hns
  have hj : 1490 ≤ 2*k-12 := by omega
  have hindex : 2*k-12+10=2*k-2 := by omega
  have hmpos : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2*k-2)
  refine ⟨P₁, P₂, hP₁, hP₂, hd₁, hd₂, ht₁, ht₂, hlog₁, hlog₂,
    hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂, ?_, ?_⟩
  · intro R hR v hv
    apply actualHarmonic_twoPower_cubic_gain_thirtysecond F hc v hv hR
      (mul_pos hmpos hd₁) hj
    simpa only [hindex] using hsave₁ v hv
  · intro R hR v hv hclose
    apply actualHarmonic_twoPower_cubic_gain_thirtysecond F hc v hv hR
      (mul_pos hmpos hd₂) hj
    simpa only [hindex] using hsave₂ v hv hclose

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_tilted_twoPower_savings
