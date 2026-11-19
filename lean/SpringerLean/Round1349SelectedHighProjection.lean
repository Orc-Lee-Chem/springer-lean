import SpringerLean.Round1348TwoActualHighEnds
import SpringerLean.Round1339SecondHighChord

open scoped ComplexConjugate

namespace SpringerLean

/-- With both selected radii above `39/20`, each high-radius hull point
obeys the same `e+5e²` projection law in the half-plane assigned to
its selected endpoint. The two halves share the actual boundary line. -/
theorem exteriorOmitted_selected_two_high_projection
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) ≤ ‖P₁‖)
    (hR₂ : (39/20 : ℝ) ≤ ‖P₂‖)
    (hwr : (39/20 : ℝ) ≤ ‖w‖)
    (hP₁max : ∀ z ∈ convexHull ℝ (exteriorOmitted F), ‖z‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ z ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*z).re ≤ 0 → ‖z‖ ≤ ‖P₂‖) :
    let e : ℝ := 2-‖w‖
    (0 ≤ (conj (P₁/(‖P₁‖ : ℂ))*w).re →
      2-(conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ e+5*e^2) ∧
    ((conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 →
      2-(conj (P₂/(‖P₂‖ : ℂ))*w).re ≤ e+5*e^2) := by
  dsimp only
  let ξ₁ : ℂ := P₁/(‖P₁‖ : ℂ)
  let ξ₂ : ℂ := P₂/(‖P₂‖ : ℂ)
  have hR₁pos : 0 < ‖P₁‖ := by linarith
  have hR₂pos : 0 < ‖P₂‖ := by linarith
  have hR₁0 : (‖P₁‖ : ℂ) ≠ 0 := by exact_mod_cast hR₁pos.ne'
  have hR₂0 : (‖P₂‖ : ℂ) ≠ 0 := by exact_mod_cast hR₂pos.ne'
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
  have hP₁form : P₁ = ξ₁*(‖P₁‖ : ℂ) := by
    dsimp [ξ₁]
    field_simp
  have hP₂form : P₂ = ξ₂*(‖P₂‖ : ℂ) := by
    dsimp [ξ₂]
    field_simp
  constructor
  · intro hpositive
    exact exteriorOmitted_forward_half_projection_five F hc P₁ w
      hP₁ hw hR₁ hwr (hP₁max w hw) hpositive
  · intro hnegative
    have hR₂maxw := hP₂max w hw hnegative
    exact exteriorOmitted_opposite_half_second_projection_five
      F hc P₁ P₂ w ξ₁ ξ₂ hP₁ hP₂ hw hξ₁ hξ₂ hP₁form hP₂form
      hR₁ hR₂ hwr (hP₁max w hw) (hP₁max P₂ hP₂)
      hR₂maxw hnegative hP₂neg

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_selected_two_high_projection
