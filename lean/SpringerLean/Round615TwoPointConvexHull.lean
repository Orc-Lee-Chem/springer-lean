import SpringerLean.Round614TwoOmittedPoints
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

namespace SpringerLean
set_option Elab.async false

noncomputable def omittedTwoPointCost (A P : ℂ) : ℝ :=
  4 * ‖A - P‖ + ‖A + P‖ ^ 2

theorem omittedTwoPointCost_symm (A P : ℂ) :
    omittedTwoPointCost A P = omittedTwoPointCost P A := by
  simp only [omittedTwoPointCost, norm_sub_rev A P, add_comm A P]

theorem omittedTwoPointCost_convex (P : ℂ) :
    ConvexOn ℝ Set.univ (fun A : ℂ => omittedTwoPointCost A P) := by
  let M : ℂ →ᵃ[ℝ] ℂ := AffineMap.id ℝ ℂ - AffineMap.const ℝ ℂ P
  let T : ℂ →ᵃ[ℝ] ℂ := AffineMap.id ℝ ℂ + AffineMap.const ℝ ℂ P
  have hm : ConvexOn ℝ Set.univ (fun A : ℂ => ‖A - P‖) := by
    have he := (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℂ → ℝ)).comp_affineMap M
    simpa [M,Function.comp_def] using he
  have hs0 : ConvexOn ℝ Set.univ (fun A : ℂ => ‖A‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro A hA B hB a b ha hb hab
    have hn : ‖a • A + b • B‖ ≤ a * ‖A‖ + b * ‖B‖ := by
      calc
        _ ≤ ‖a • A‖ + ‖b • B‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
    have hpos : 0 ≤ a * ‖A‖ + b * ‖B‖ := by positivity
    have hsq := (sq_le_sq₀ (norm_nonneg _) hpos).mpr hn
    have hid : (a + b) * (a * ‖A‖ ^ 2 + b * ‖B‖ ^ 2) -
        (a * ‖A‖ + b * ‖B‖) ^ 2 = a * b * (‖A‖ - ‖B‖) ^ 2 := by ring
    rw [hab, one_mul] at hid
    have hvar := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖A‖ - ‖B‖))
    simp only [smul_eq_mul]
    nlinarith
  have ht : ConvexOn ℝ Set.univ (fun A : ℂ => ‖A + P‖ ^ 2) := by
    have he := hs0.comp_affineMap T
    simpa [T,Function.comp_def] using he
  refine ⟨convex_univ, ?_⟩
  intro A hA B hB a b ha hb hab
  have h1 := hm.2 hA hB ha hb hab
  have h2 := ht.2 hA hB ha hb hab
  change 4 * ‖a • A + b • B - P‖ + ‖a • A + b • B + P‖ ^ 2 ≤
    a * (4 * ‖A - P‖ + ‖A + P‖ ^ 2) + b * (4 * ‖B - P‖ + ‖B + P‖ ^ 2)
  simp only [smul_eq_mul] at h1 h2
  nlinarith

theorem omittedTwoPointCost_sublevel_convex (P : ℂ) :
    Convex ℝ {A : ℂ | omittedTwoPointCost A P ≤ 16} := by
  simpa only [Set.mem_univ, true_and] using (omittedTwoPointCost_convex P).convex_le 16

/-- Corrected manuscript br:two, with both points in the ordinary real
convex hull of the actual omitted set. No geometric estimate is a premise. -/
theorem exteriorOmitted_convexHull_two_point
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ convexHull ℝ (exteriorOmitted F))
    (hP : P ∈ convexHull ℝ (exteriorOmitted F)) :
    4 * ‖A - P‖ + ‖A + P‖ ^ 2 ≤ 16 := by
  have hfirst : ∀ P ∈ exteriorOmitted F,
      ∀ A ∈ convexHull ℝ (exteriorOmitted F), omittedTwoPointCost A P ≤ 16 := by
    intro P hP A hA
    have hsub : exteriorOmitted F ⊆ {A : ℂ | omittedTwoPointCost A P ≤ 16} := by
      intro A hA
      exact exteriorOmitted_two_point F hc A P hA hP
    exact convexHull_min hsub (omittedTwoPointCost_sublevel_convex P) hA
  have hsub : exteriorOmitted F ⊆ {P : ℂ | omittedTwoPointCost P A ≤ 16} := by
    intro P hP
    change omittedTwoPointCost P A ≤ 16
    rw [omittedTwoPointCost_symm P A]
    exact hfirst P hP A hA
  have he := convexHull_min hsub (omittedTwoPointCost_sublevel_convex A) hP
  change omittedTwoPointCost P A ≤ 16 at he
  rwa [omittedTwoPointCost_symm P A] at he

/-- The annular two-point clustering input, with the full quadratic deficit
retained. The weaker16e follows immediately when needed. -/
theorem exteriorOmitted_pair_distance_deficit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ convexHull ℝ (exteriorOmitted F))
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    {e : ℝ} (he0 : 0 ≤ e) (he2 : e ≤ 2)
    (hAr : 2 - e ≤ ‖A‖) (hPr : 2 - e ≤ ‖P‖) :
    ‖A - P‖ * (4 - ‖A - P‖) ≤ 16 * e - 4 * e ^ 2 := by
  have ht := exteriorOmitted_convexHull_two_point F hc A P hA hP
  have hl := parallelogram_law_with_norm ℂ A P
  have hsA : (2 - e) ^ 2 ≤ ‖A‖ ^ 2 :=
    (sq_le_sq₀ (by linarith) (norm_nonneg _)).mpr hAr
  have hsP : (2 - e) ^ 2 ≤ ‖P‖ ^ 2 :=
    (sq_le_sq₀ (by linarith) (norm_nonneg _)).mpr hPr
  nlinarith

end SpringerLean
