import SpringerLean.Round1413SecondAssignedProjection
import SpringerLean.Round1409ActualAffineCap

open scoped ComplexConjugate

namespace SpringerLean

/-- Both selected sides now have the actual refined affine radius cap
on the whole ordinary convex hull. The dividing line may be counted
once in subsequent integration. -/
theorem exteriorOmitted_selected_two_assigned_affine_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ exteriorOmitted F)
    (hP₂ : P₂ ∈ exteriorOmitted F)
    (hR₁ : (39/20 : ℝ) ≤ ‖P₁‖)
    (hR₂ : (39/20 : ℝ) ≤ ‖P₂‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hd₁ : 0 < 2-‖P₁‖) (hd₂ : 0 < 2-‖P₂‖)
    (hdef₁ : ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 1)
    (hdef₂ : ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 1) :
    let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
      (1+Real.sqrt (2-‖P₁‖)/10))^2
    let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
      (1+Real.sqrt (2-‖P₂‖)/10))^2
    (∀ w ∈ convexHull ℝ (exteriorOmitted F),
      0 ≤ (conj (P₁/(‖P₁‖:ℂ))*w).re →
      ‖w‖ ≤ max (19/10 : ℝ)
        (2-(1-(107/100 : ℝ)*W₁)*
          (2-(conj (P₁/(‖P₁‖:ℂ))*w).re)+(107/100 : ℝ)*W₁^2)) ∧
    (∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 →
      ‖w‖ ≤ max (19/10 : ℝ)
        (2-(1-(107/100 : ℝ)*W₂)*
          (2-(conj (P₂/(‖P₂‖:ℂ))*w).re)+(107/100 : ℝ)*W₂^2)) := by
  dsimp only
  have hP₁Hull : P₁ ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ _ hP₁
  have hP₂Hull : P₂ ∈ convexHull ℝ (exteriorOmitted F) :=
    subset_convexHull ℝ _ hP₂
  constructor
  · intro w hw hfw
    exact exteriorOmitted_actualEndpoint_positive_affine_cap
      F hc k hk P₁ hP₁ hd₁ hdef₁ w hw hfw
  · intro w hw hfar
    by_cases hsmall : ‖w‖ ≤ (19/10 : ℝ)
    · exact hsmall.trans (le_max_left _ _)
    · have hwr : (19/10 : ℝ) ≤ ‖w‖ :=
        le_of_lt (lt_of_not_ge hsmall)
      have hpositive := exteriorOmitted_selected_second_assigned_projection_nonneg
        F hc P₁ P₂ w hP₁Hull hP₂Hull hw hR₁ hR₂ hwr
        hP₁max hP₂neg hP₂max hfar
      exact exteriorOmitted_actualEndpoint_positive_affine_cap
        F hc k hk P₂ hP₂ hd₂ hdef₂ w hw hpositive

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_selected_two_assigned_affine_caps
