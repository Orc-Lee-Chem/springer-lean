import SpringerLean.Round1495SecondGlobalCap

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- Actual omitted endpoints with the selected opposite-half maximum and
fine first-end width give a full-hull cap in the second direction. -/
theorem exteriorOmitted_actual_selected_second_global_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F)
    (hd₁ : 0 < 2-‖P₁‖)
    (ht₁ : ((2*k-1:ℕ):ℝ)*(2-‖P₁‖)<3/20)
    (hd₂ : 0 < 2-‖P₂‖)
    (ht₂ : ((2*k-1:ℕ):ℝ)*(2-‖P₂‖)<3/20)
    (hmW₁ : ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P₁<1/2)
    (hneg : (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0)
    (hmax₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ ‖P₂‖ := by
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hmNat : 1500 ≤ 2*k-2 := by omega
  have hn : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hm : (1500:ℝ) ≤ ((2*k-2:ℕ):ℝ) := by exact_mod_cast hmNat
  have hR₁le : ‖P₁‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP₁
  have hR₁ : 0 < ‖P₁‖ := by
    have hmul := mul_le_mul_of_nonneg_right hn hd₁.le
    nlinarith
  have hR₂ : 1 < ‖P₂‖ := by
    have hmul := mul_le_mul_of_nonneg_right hn hd₂.le
    nlinarith
  let W := exteriorFineEndpointWidth P₁
  have hW0 : 0 ≤ W := by
    dsimp [W,exteriorFineEndpointWidth]
    exact sq_nonneg _
  have hW : W < 1/3000 := by
    have hmul := mul_le_mul_of_nonneg_right hm hW0
    dsimp [W] at hmW₁ ⊢
    nlinarith
  have hstrip : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).im^2 ≤
        4*W*(W+‖P₁‖-(conj (P₁/(‖P₁‖:ℂ))*w).re) := by
    intro w hw
    have hs := exteriorOmitted_actualEndpoint_fine_strip
      F hc k hk P₁ hP₁ hd₁ ht₁ w hw
    exact hs.2.1
  exact selectedEndpoints_second_full_axis_cap F P₁ P₂ W
    hR₁ hR₁le hR₂ hW0 hW hneg hmax₂ hstrip

/-- The same actual selected pair has fine widths and full projection
caps in both directions. This is the cap input for the inner-circle
truncated Poisson comparison. -/
theorem exteriorInverseCoeff_candidate_selected_two_global_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖)*
        Real.log (2/(2-‖P₁‖)) < 3/2 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖)*
        Real.log (2/(2-‖P₂‖)) < 3/2 ∧
      exteriorFineEndpointWidth P₁ <
        (1/3:ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) ∧
      exteriorFineEndpointWidth P₂ <
        (1/3:ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) ∧
      ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P₁ < 1/2 ∧
      ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P₂ < 1/2 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ ‖P₁‖) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ ‖P₂‖) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hlog₁,hlog₂,
    hW₁,hW₂,hmW₁,hmW₂,hmax₁,hneg,hmax₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_fine_widths
      F hc k hk hB hns
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hR₁ : 0 < ‖P₁‖ := by
    have hmul := mul_le_mul_of_nonneg_right hn hd₁.le
    nlinarith
  have hR₂ : 0 < ‖P₂‖ := by
    have hmul := mul_le_mul_of_nonneg_right hn hd₂.le
    nlinarith
  have hcap₁ := (selectedEndpoints_assigned_axis_caps
    F P₁ P₂ hR₁ hR₂ hmax₁ hmax₂).1
  have hcap₂ := exteriorOmitted_actual_selected_second_global_cap
    F hc k hk P₁ P₂ hP₁ hd₁ ht₁ hd₂ ht₂ hmW₁ hneg hmax₂
  exact ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hlog₁,hlog₂,
    hW₁,hW₂,hmW₁,hmW₂,hmax₁,hneg,hmax₂,hcap₁,hcap₂⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actual_selected_second_global_cap
#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_global_caps
