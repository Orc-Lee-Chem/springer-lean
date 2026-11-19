import SpringerLean.Round616CuttingLine
import SpringerLean.Round617HalfMaximizerOmitted

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- Once the two actual hull radii have been located, the opposite
maximizer is in the actual omitted set. No boundary or extreme-point
regularity is assumed. -/
theorem exteriorOmitted_half_maximizer_mem_of_radius_bounds
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hr₁ : (237 : ℝ)/125 ≤ ‖P₁‖) (hr₂ : (8 : ℝ)/5 ≤ ‖P₂‖)
    (hhalf : (conj P₁ * P₂).re ≤ 0)
    (hmax : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj P₁ * w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    P₂ ∈ exteriorOmitted F :=
  exteriorOmitted_half_maximizer_mem_of_strict F hc P₁ P₂ hP₂
    (exteriorOmitted_negative_half_direction_strict F hc P₁ P₂
      hP₁ hP₂ hr₁ hr₂ hhalf) hmax

end SpringerLean
