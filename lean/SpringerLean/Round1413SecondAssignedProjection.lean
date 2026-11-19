import SpringerLean.Round1412MediumSecondNear

open scoped ComplexConjugate

namespace SpringerLean

/-- Every actual hull point in the selected opposite half with radius
at least 1.9 has nonnegative projection toward the same selected P2. -/
theorem exteriorOmitted_selected_second_assigned_projection_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) ≤ ‖P₁‖)
    (hR₂ : (39/20 : ℝ) ≤ ‖P₂‖)
    (hwr : (19/10 : ℝ) ≤ ‖w‖)
    (hP₁max : ∀ z ∈ convexHull ℝ (exteriorOmitted F), ‖z‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ z ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*z).re ≤ 0 → ‖z‖ ≤ ‖P₂‖)
    (hwneg : (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0) :
    0 ≤ (conj (P₂/(‖P₂‖:ℂ))*w).re := by
  let ξ₁ : ℂ := P₁/(‖P₁‖:ℂ)
  let ξ₂ : ℂ := P₂/(‖P₂‖:ℂ)
  have hR₁pos : 0 < ‖P₁‖ := by linarith
  have hR₂pos : 0 < ‖P₂‖ := by linarith
  have hP₁ne : P₁ ≠ 0 := norm_pos_iff.mp hR₁pos
  have hP₂ne : P₂ ≠ 0 := norm_pos_iff.mp hR₂pos
  have hξ₁ : ‖ξ₁‖ = 1 := by dsimp [ξ₁]; simp [hP₁ne]
  have hξ₂ : ‖ξ₂‖ = 1 := by dsimp [ξ₂]; simp [hP₂ne]
  have hR₁ne : (‖P₁‖:ℂ) ≠ 0 := by exact_mod_cast hR₁pos.ne'
  have hR₂ne : (‖P₂‖:ℂ) ≠ 0 := by exact_mod_cast hR₂pos.ne'
  have hP₁form : P₁=ξ₁*(‖P₁‖:ℂ) := by
    dsimp [ξ₁]
    field_simp [hR₁ne]
  have hP₂form : P₂=ξ₂*(‖P₂‖:ℂ) := by
    dsimp [ξ₂]
    field_simp [hR₂ne]
  have hnear := exteriorOmitted_opposite_half_second_near_451_100
    F hc P₁ P₂ w ξ₁ hP₁ hP₂ hw hξ₁ hP₁form
    (by linarith) (by linarith) hwr
    (hP₁max w hw) (hP₁max P₂ hP₂) (hP₂max w hw hwneg)
    hwneg hP₂neg
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  exact medium_near_endpoint_projection_nonneg P₂ w ξ₂ hξ₂ hP₂form
    (by linarith) hwr (by linarith) (by linarith) hnear

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_selected_second_assigned_projection_nonneg
