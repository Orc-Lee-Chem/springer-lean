import SpringerLean.Round1347SecondRadius195
import SpringerLean.Round1326SecondEndpointRadius

open scoped ComplexConjugate

namespace SpringerLean

/-- Both selected endpoints of every actual `k ≥ 751` Catalan
candidate now lie in the omitted set and have radius greater than
`39/20`. The first endpoint retains its stronger `359/180` bound. -/
theorem exteriorOmitted_exists_candidate_two_actual_endpoints195
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      P₂ ∈ exteriorOmitted F ∧
      (39/20 : ℝ) < ‖P₂‖ ∧
      (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) := by
  obtain ⟨P₁,P₂,hP₁,hR₁,hmax,hP₂,_hR₂,hneg,hhalf⟩ :=
    exteriorOmitted_exists_candidate_two_actual_endpoints359 F hc k hk hB
  have hP₁hull : P₁ ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ _ hP₁
  have hR₂ := exteriorOmitted_candidate_second_radius_gt_39_20
    F hc k hk hB P₁ P₂ hP₁hull hR₁ hmax hhalf
  exact ⟨P₁,P₂,hP₁,hR₁,hmax,hP₂,hR₂,hneg,hhalf⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_exists_candidate_two_actual_endpoints195
