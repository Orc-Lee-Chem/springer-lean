import SpringerLean.Round1400StrictChordSaving
import SpringerLean.Round1371DeficitIntegralReduction
import SpringerLean.Round1326SecondEndpointRadius
import SpringerLean.Round1347SecondRadius195

open scoped ComplexConjugate

namespace SpringerLean

/-- The two exact circle inequalities have now been discharged, so
the Round1371 actual-function reduction has no scalar hypotheses. -/
theorem candidate_selected_radii_gt_two_sub_inv_order
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F)
    (hP₂ : P₂ ∈ exteriorOmitted F)
    (hP₁big : (359/180 : ℝ) < ‖P₁‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    (2-1/(((2*k-1:ℕ):ℝ)) < ‖P₁‖) ∧
    (2-1/(((2*k-1:ℕ):ℝ)) < ‖P₂‖) := by
  have hP₁Hull : P₁ ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ _ hP₁
  have hP₂Hull : P₂ ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ _ hP₂
  have hR₁ : (39/20 : ℝ) < ‖P₁‖ := by linarith
  have hR₂ := exteriorOmitted_candidate_second_radius_gt_39_20
    F hc k hk hB P₁ P₂ hP₁Hull hP₁big hP₁max hP₂max
  have hmodel := coarseInverseModelCircle_le_thirteen (2*k-1)
    (by omega : 1 ≤ 2*k-1)
  have hsaving := coarseInverseChord_strict_circle_saving k hk
  exact candidate_selected_deficits_lt_one_of_exact_circle_bounds
    F hc k hk hB P₁ P₂ hP₁Hull hP₂Hull hR₁ hR₂
    hP₁max hP₂neg hP₂max hmodel (by simpa using hsaving)

/-- Both actual, selected omitted points have `0≤n dᵢ<1` under the
weak Catalan candidate, including equality. -/
theorem exteriorOmitted_exists_candidate_two_actual_deficits_lt_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧
      P₂ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      0 ≤ (((2*k-1:ℕ):ℝ))*(2-‖P₁‖) ∧
      (((2*k-1:ℕ):ℝ))*(2-‖P₁‖) < 1 ∧
      0 ≤ (((2*k-1:ℕ):ℝ))*(2-‖P₂‖) ∧
      (((2*k-1:ℕ):ℝ))*(2-‖P₂‖) < 1 := by
  obtain ⟨P₁,P₂,hP₁,hP₁big,hP₁max,hP₂,hP₂big,hP₂neg,hP₂max⟩ :=
    exteriorOmitted_exists_candidate_two_actual_endpoints359 F hc k hk hB
  have hrad := candidate_selected_radii_gt_two_sub_inv_order
    F hc k hk hB P₁ P₂ hP₁ hP₂ hP₁big hP₁max hP₂neg hP₂max
  have hP₁le : ‖P₁‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP₁
  have hP₂le : ‖P₂‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP₂
  have hn : (0:ℝ) < ((2*k-1:ℕ):ℝ) := by
    exact_mod_cast (by omega : 0<2*k-1)
  have h₁ : 0 ≤ (((2*k-1:ℕ):ℝ))*(2-‖P₁‖) :=
    mul_nonneg hn.le (by linarith)
  have h₂ : 0 ≤ (((2*k-1:ℕ):ℝ))*(2-‖P₂‖) :=
    mul_nonneg hn.le (by linarith)
  have h₁lt : (((2*k-1:ℕ):ℝ))*(2-‖P₁‖)<1 := by
    have hh := hrad.1
    have hdef : 2-‖P₁‖ < 1/(((2*k-1:ℕ):ℝ)) := by linarith
    have hmul := (lt_div_iff₀ hn).1 hdef
    nlinarith
  have h₂lt : (((2*k-1:ℕ):ℝ))*(2-‖P₂‖)<1 := by
    have hh := hrad.2
    have hdef : 2-‖P₂‖ < 1/(((2*k-1:ℕ):ℝ)) := by linarith
    have hmul := (lt_div_iff₀ hn).1 hdef
    nlinarith
  exact ⟨P₁,P₂,hP₁,hP₂,hP₁big,hP₁max,hP₂neg,hP₂max,
    h₁,h₁lt,h₂,h₂lt⟩

end SpringerLean

#print axioms SpringerLean.candidate_selected_radii_gt_two_sub_inv_order
#print axioms SpringerLean.exteriorOmitted_exists_candidate_two_actual_deficits_lt_one
