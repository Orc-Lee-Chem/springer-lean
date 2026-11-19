import SpringerLean.Round1489SelectedJointJ
import SpringerLean.Round1470JFloor

open scoped ComplexConjugate

namespace SpringerLean

/-- Joint localization and the uniform cubic floor isolate each of
the two selected actual endpoint deficits below the `0.58` threshold. -/
theorem exteriorInverseCoeff_candidate_selected_each_J_lt_058
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 1 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 1 ∧
      refinedAffineJ (2*k-1)
        (((2*k-1:ℕ):ℝ)*(2-‖P₁‖)) < 58/100 ∧
      refinedAffineJ (2*k-1)
        (((2*k-1:ℕ):ℝ)*(2-‖P₂‖)) < 58/100 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hdef₁,hdef₂,hjoint,
    hmax₁,hneg,hmax₂⟩ :=
    exteriorInverseCoeff_candidate_selected_joint_J
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  let t₁ : ℝ := (n:ℝ)*(2-‖P₁‖)
  let t₂ : ℝ := (n:ℝ)*(2-‖P₂‖)
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hn0 : (0:ℝ)<n := by
    exact_mod_cast (by omega : 0<n)
  have ht₁ : 0 < t₁ := mul_pos hn0 hd₁
  have ht₂ : 0 < t₂ := mul_pos hn0 hd₂
  have hfloor₁ := refinedAffineJ_floor n hn ht₁ hdef₁
  have hfloor₂ := refinedAffineJ_floor n hn ht₂ hdef₂
  change refinedAffineJ n t₁+refinedAffineJ n t₂ < 52/100 at hjoint
  refine ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hdef₁,hdef₂,?_,?_,hmax₁,hneg,hmax₂⟩
  · change refinedAffineJ n t₁ < 58/100
    nlinarith [hjoint,hfloor₂]
  · change refinedAffineJ n t₂ < 58/100
    nlinarith [hjoint,hfloor₁]

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_each_J_lt_058
