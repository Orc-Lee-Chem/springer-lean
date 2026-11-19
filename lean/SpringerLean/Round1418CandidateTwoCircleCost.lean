import SpringerLean.Round1417RefinedTwoCircleCost
import SpringerLean.Round1415CandidateTwoAffineCaps

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual nonslit weak Catalan candidate now reaches the two
normalized comparison-circle integrals of its own selected endpoint
widths. No trace or finite certificate is assumed. -/
theorem exteriorInverseCoeff_candidate_two_refined_circle_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧ (39/20 : ℝ) < ‖P₂‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      (((2*k-1:ℕ):ℝ)*(2-‖P₁‖)) < 1 ∧
      (((2*k-1:ℕ):ℝ)*(2-‖P₂‖)) < 1 ∧
      (let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
        (1+Real.sqrt (2-‖P₁‖)/10))^2
       let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
        (1+Real.sqrt (2-‖P₂‖)/10))^2
       ((2*k-1:ℕ):ℝ)*‖exteriorInverseCoeff F (2*k-1)‖ ≤
         Real.circleAverage
           (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^(2*k-1)) 0 1 +
         Real.circleAverage
           (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^(2*k-1)) 0 1) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hmax₁,hneg,hmax₂,
    hd₁,hd₂,hdef₁,hdef₂,hcaps⟩ :=
    exteriorOmitted_exists_candidate_two_assigned_affine_caps
      F hc k hk hB hns
  let ξ₁ : ℂ := P₁/(‖P₁‖:ℂ)
  let ξ₂ : ℂ := P₂/(‖P₂‖:ℂ)
  let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
    (1+Real.sqrt (2-‖P₁‖)/10))^2
  let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
    (1+Real.sqrt (2-‖P₂‖)/10))^2
  have hP₁ne : P₁ ≠ 0 := by
    intro hp
    simp [hp] at hR₁
    norm_num at hR₁
  have hP₂ne : P₂ ≠ 0 := by
    intro hp
    simp [hp] at hR₂
    norm_num at hR₂
  have hξ₁ : ‖ξ₁‖=1 := by dsimp [ξ₁]; simp [hP₁ne]
  have hξ₂ : ‖ξ₂‖=1 := by dsimp [ξ₂]; simp [hP₂ne]
  have hcover : ∀ w ∈ exteriorOmitted F,
      ‖w‖ ≤ refinedAffineRadius W₁ (conj ξ₁*w).re ∨
      ‖w‖ ≤ refinedAffineRadius W₂ (conj ξ₂*w).re := by
    intro w hw
    have hwHull : w ∈ convexHull ℝ (exteriorOmitted F) :=
      subset_convexHull ℝ _ hw
    by_cases hforward : 0 ≤ (conj ξ₁*w).re
    · left
      have hh := hcaps.1 w hwHull hforward
      simpa only [refinedAffineRadius,ξ₁,W₁] using hh
    · right
      have hfar : (conj ξ₁*w).re ≤ 0 :=
        le_of_lt (lt_of_not_ge hforward)
      have hh := hcaps.2 w hwHull hfar
      simpa only [refinedAffineRadius,ξ₂,W₂] using hh
  have hcost := exteriorInverseCoeff_le_of_two_refinedAffine_caps
    F hc (2*k-1) (by omega) ξ₁ ξ₂ hξ₁ hξ₂ W₁ W₂ hcover
  exact ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hmax₁,hneg,hmax₂,
    hd₁,hd₂,hdef₁,hdef₂,hcost⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_two_refined_circle_cost
