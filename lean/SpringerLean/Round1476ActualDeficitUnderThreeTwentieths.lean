import SpringerLean.Round1475JLargeDeficitExclusion

namespace SpringerLean

/-- The same selected actual omitted endpoints from the two-chord
candidate comparison both have normalized deficits below `3/20`.
No extra assumption beyond the original mapping class and weak
Catalan candidate enters this localization. -/
theorem exteriorInverseCoeff_candidate_actual_both_deficits_lt_3_20
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 3/20 := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hJ₁,hJ₂⟩ :=
    exteriorInverseCoeff_candidate_actual_each_J_lt_058
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hzero₁ : 0 < (n:ℝ)*(2-‖P₁‖) := mul_pos hn0 hd₁
  have hzero₂ : 0 < (n:ℝ)*(2-‖P₂‖) := mul_pos hn0 hd₂
  have hsmall₁ : (n:ℝ)*(2-‖P₁‖) < 3/20 := by
    by_contra h
    have hlarge : (3/20:ℝ) ≤ (n:ℝ)*(2-‖P₁‖) := by linarith
    have hbad := refinedAffineJ_large_deficit_gt_058 n hn hlarge ht₁.le
    linarith
  have hsmall₂ : (n:ℝ)*(2-‖P₂‖) < 3/20 := by
    by_contra h
    have hlarge : (3/20:ℝ) ≤ (n:ℝ)*(2-‖P₂‖) := by linarith
    have hbad := refinedAffineJ_large_deficit_gt_058 n hn hlarge ht₂.le
    linarith
  exact ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hsmall₁,hsmall₂⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_actual_both_deficits_lt_3_20
