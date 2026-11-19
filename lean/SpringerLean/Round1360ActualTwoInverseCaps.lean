import SpringerLean.Round1359ExactInverseProfileScalar
import SpringerLean.Round1349SelectedHighProjection

open scoped ComplexConjugate

namespace SpringerLean

/-- The selected two endpoints control every point of the actual
ordinary convex hull by one of the exact inverse-square-root profiles.
This is the geometric cap needed for the short circle Jacobian estimate. -/
theorem exteriorOmitted_selected_two_inverse_radius_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) < ‖P₁‖)
    (hR₂ : (39/20 : ℝ) < ‖P₂‖)
    (hP₁max : ∀ z ∈ convexHull ℝ (exteriorOmitted F), ‖z‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ z ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*z).re ≤ 0 → ‖z‖ ≤ ‖P₂‖) :
    (‖w‖ ≤ coarseInverseRadius ((conj (P₁/(‖P₁‖ : ℂ))*w).re) ∧
      ‖w‖ ≤ ‖P₁‖) ∨
    (‖w‖ ≤ coarseInverseRadius ((conj (P₂/(‖P₂‖ : ℂ))*w).re) ∧
      ‖w‖ ≤ ‖P₂‖) := by
  let ξ₁ : ℂ := P₁/(‖P₁‖ : ℂ)
  let ξ₂ : ℂ := P₂/(‖P₂‖ : ℂ)
  let x₁ : ℝ := (conj ξ₁*w).re
  let x₂ : ℝ := (conj ξ₂*w).re
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hP₁ne : P₁ ≠ 0 := by
    intro hp
    simp [hp] at hR₁
    norm_num at hR₁
  have hP₂ne : P₂ ≠ 0 := by
    intro hp
    simp [hp] at hR₂
    norm_num at hR₂
  have hξ₁ : ‖ξ₁‖ = 1 := by dsimp [ξ₁]; simp [hP₁ne]
  have hξ₂ : ‖ξ₂‖ = 1 := by dsimp [ξ₂]; simp [hP₂ne]
  have hx₁ : x₁ ≤ ‖w‖ := by
    calc
      x₁ = (conj ξ₁*w).re := rfl
      _ ≤ ‖conj ξ₁*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by simp [norm_mul, hξ₁]
  have hx₂ : x₂ ≤ ‖w‖ := by
    calc
      x₂ = (conj ξ₂*w).re := rfl
      _ ≤ ‖conj ξ₂*w‖ := Complex.re_le_norm _
      _ = ‖w‖ := by simp [norm_mul, hξ₂]
  by_cases hsmall : ‖w‖ ≤ (39/20 : ℝ)
  · left
    exact ⟨hsmall.trans (coarseInverseRadius_ge_platform_of_le_two
      (hx₁.trans hw2)), hP₁max w hw⟩
  · have hwr : (39/20 : ℝ) ≤ ‖w‖ := le_of_lt (lt_of_not_ge hsmall)
    have hgeom := exteriorOmitted_selected_two_high_projection F hc
      P₁ P₂ w hP₁ hP₂ hw hR₁.le hR₂.le hwr hP₁max
      hP₂neg hP₂max
    by_cases hpos : 0 ≤ x₁
    · left
      exact ⟨coarseInverseRadius_ge_radius hwr hw2 hx₁ (hgeom.1 hpos),
        hP₁max w hw⟩
    · right
      have hneg : x₁ ≤ 0 := le_of_lt (lt_of_not_ge hpos)
      exact ⟨coarseInverseRadius_ge_radius hwr hw2 hx₂
        (hgeom.2 hneg), hP₂max w hw hneg⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_selected_two_inverse_radius_cap
