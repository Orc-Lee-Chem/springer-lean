import SpringerLean.Round1414TwoAssignedAffineCaps
import SpringerLean.Round487EndpointRadius

open scoped ComplexConjugate

namespace SpringerLean

/-- A nonslit actual weak Catalan candidate has two selected omitted
endpoints with positive localized deficits, and each assigned half of
the ordinary hull is covered by its own refined affine radius test. -/
theorem exteriorOmitted_exists_candidate_two_assigned_affine_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧
      (39/20 : ℝ) < ‖P₂‖ ∧
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
       (∀ w ∈ convexHull ℝ (exteriorOmitted F),
          0 ≤ (conj (P₁/(‖P₁‖:ℂ))*w).re →
          ‖w‖ ≤ max (19/10 : ℝ)
            (2-(1-(107/100 : ℝ)*W₁)*
              (2-(conj (P₁/(‖P₁‖:ℂ))*w).re)+(107/100 : ℝ)*W₁^2)) ∧
       (∀ w ∈ convexHull ℝ (exteriorOmitted F),
          (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 →
          ‖w‖ ≤ max (19/10 : ℝ)
            (2-(1-(107/100 : ℝ)*W₂)*
              (2-(conj (P₂/(‖P₂‖:ℂ))*w).re)+(107/100 : ℝ)*W₂^2))) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hbig,hmax₁,hneg,hmax₂,
    hd₁nonneg,hd₁lt,hd₂nonneg,hd₂lt⟩ :=
    exteriorOmitted_exists_candidate_two_actual_deficits_lt_one F hc k hk hB
  have hd₁pos : 0 < 2-‖P₁‖ := by
    have hh := exteriorOmitted_convexHull_norm_lt_two_of_not_slit
      F hc hns (subset_convexHull ℝ _ hP₁)
    linarith
  have hd₂pos : 0 < 2-‖P₂‖ := by
    have hh := exteriorOmitted_convexHull_norm_lt_two_of_not_slit
      F hc hns (subset_convexHull ℝ _ hP₂)
    linarith
  have hR₁ : (39/20 : ℝ) ≤ ‖P₁‖ := by linarith
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501 : ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hm := mul_le_mul_of_nonneg_right hn hd₂pos.le
  have hR₂ : (39/20 : ℝ) ≤ ‖P₂‖ := by nlinarith
  have hR₂strict : (39/20 : ℝ) < ‖P₂‖ := by nlinarith
  have hcaps := exteriorOmitted_selected_two_assigned_affine_caps
    F hc k hk P₁ P₂ hP₁ hP₂ hR₁ hR₂ hmax₁ hneg hmax₂
    hd₁pos hd₂pos hd₁lt hd₂lt
  exact ⟨P₁,P₂,hP₁,hP₂,hbig,hR₂strict,hmax₁,hneg,hmax₂,
    hd₁pos,hd₂pos,hd₁lt,hd₂lt,hcaps⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_exists_candidate_two_assigned_affine_caps
