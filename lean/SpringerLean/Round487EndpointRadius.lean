import SpringerLean.Round401EndpointChoices
import SpringerLean.Round481OmittedRadiusRigidity

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem exteriorOmitted_convexHull_norm_lt_two_of_not_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hns : ¬∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk)
    {w : ℂ} (hw : w ∈ convexHull ℝ (exteriorOmitted F)) : ‖w‖ < 2 := by
  obtain ⟨P, hP, hmax⟩ := exteriorOmitted_exists_radius_maximizer F hc
  have hle := exteriorOmitted_norm_le_two F hc hP
  have hne : ‖P‖ ≠ 2 := by
    intro he
    exact hns (exteriorOmitted_norm_eq_two_implies_slit F hc hP he)
  exact lt_of_le_of_lt (hmax w hw) (lt_of_le_of_ne hle hne)

/-- Preliminary actual endpoint selection. The second point is in the hull;
its membership in K and the quantitative n*d localization are NOT asserted. -/
theorem exteriorOmitted_exists_endpoints_with_nonnegative_deficits
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ P₁ P₂ : ℂ, P₁ ∈ exteriorOmitted F ∧ P₁ ≠ 0 ∧
      P₂ ∈ convexHull ℝ (exteriorOmitted F) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      Complex.re (conj (P₁ / (‖P₁‖ : ℂ)) * P₂) ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        Complex.re (conj (P₁ / (‖P₁‖ : ℂ)) * w) ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      0 ≤ 2 - ‖P₁‖ ∧ 2 - ‖P₁‖ < 2 ∧
      0 ≤ 2 - ‖P₂‖ ∧ 2 - ‖P₂‖ ≤ 2 := by
  obtain ⟨P₁, hP₁, hn₁, hm₁⟩ := exteriorOmitted_exists_nonzero_radius_maximizer F hc
  obtain ⟨P₂, hP₂, hd₂, hm₂⟩ :=
    exteriorOmitted_exists_half_radius_maximizer F hc (P₁ / (‖P₁‖ : ℂ))
  refine ⟨P₁, P₂, hP₁, hn₁, hP₂, hm₁, hd₂, hm₂, ?_, ?_, ?_, ?_⟩
  · linarith [exteriorOmitted_norm_le_two F hc hP₁]
  · linarith [norm_pos_iff.mpr hn₁]
  · linarith [exteriorOmitted_convexHull_norm_le_two F hc hP₂]
  · linarith [norm_nonneg P₂]

end SpringerLean
