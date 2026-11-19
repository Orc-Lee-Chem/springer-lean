import SpringerLean.Round1480SmallJExclusion

namespace SpringerLean
set_option maxHeartbeats 180000

/-- The sharp logarithmic localization for both actual selected
omitted endpoints. All hypotheses are exactly from the original
mapping class and the weak Catalan candidate. -/
theorem exteriorInverseCoeff_candidate_actual_both_log_deficits_lt_3_2
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
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖)*
        Real.log (2/(2-‖P₁‖)) < 3/2 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖)*
        Real.log (2/(2-‖P₂‖)) < 3/2 := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hJ₁,hJ₂⟩ :=
    exteriorInverseCoeff_candidate_actual_each_J_lt_058
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  let N : ℝ := n
  let d₁ : ℝ := 2-‖P₁‖
  let d₂ : ℝ := 2-‖P₂‖
  let t₁ : ℝ := N*d₁
  let t₂ : ℝ := N*d₂
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hn1 : 1 ≤ n := by omega
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast (by omega : 0<n)
  have ht₁0 : 0 < t₁ := mul_pos hN0 hd₁
  have ht₂0 : 0 < t₂ := mul_pos hN0 hd₂
  have hsmall₁ : t₁ < 3/20 := by
    by_contra h
    have hlarge : (3/20:ℝ) ≤ t₁ := by linarith
    have hbad := refinedAffineJ_large_deficit_gt_058 n hn hlarge ht₁.le
    linarith
  have hsmall₂ : t₂ < 3/20 := by
    by_contra h
    have hlarge : (3/20:ℝ) ≤ t₂ := by linarith
    have hbad := refinedAffineJ_large_deficit_gt_058 n hn hlarge ht₂.le
    linarith
  have hz₁ := refinedAffineJ_small_z_lt_051 n hn ht₁0 hsmall₁.le hJ₁
  have hz₂ := refinedAffineJ_small_z_lt_051 n hn ht₂0 hsmall₂.le hJ₂
  have heq₁ := refinedAffine_z_deficit_eq hn1 hd₁
  have heq₂ := refinedAffine_z_deficit_eq hn1 hd₂
  change (17/50:ℝ)*t₁*Real.log (2*N/t₁) =
    N*((17/50:ℝ)*d₁*Real.log (2/d₁)) at heq₁
  change (17/50:ℝ)*t₂*Real.log (2*N/t₂) =
    N*((17/50:ℝ)*d₂*Real.log (2/d₂)) at heq₂
  change (17/50:ℝ)*t₁*Real.log (2*N/t₁)<51/100 at hz₁
  change (17/50:ℝ)*t₂*Real.log (2*N/t₂)<51/100 at hz₂
  have hlog₁ : t₁*Real.log (2/d₁)<3/2 := by
    have hh : (17/50:ℝ)*(t₁*Real.log (2/d₁))<51/100 := by
      calc
        _ = N*((17/50:ℝ)*d₁*Real.log (2/d₁)) := by dsimp [t₁]; ring
        _ = (17/50:ℝ)*t₁*Real.log (2*N/t₁) := heq₁.symm
        _ < 51/100 := hz₁
    nlinarith
  have hlog₂ : t₂*Real.log (2/d₂)<3/2 := by
    have hh : (17/50:ℝ)*(t₂*Real.log (2/d₂))<51/100 := by
      calc
        _ = N*((17/50:ℝ)*d₂*Real.log (2/d₂)) := by dsimp [t₂]; ring
        _ = (17/50:ℝ)*t₂*Real.log (2*N/t₂) := heq₂.symm
        _ < 51/100 := hz₂
    nlinarith
  exact ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hsmall₁,hsmall₂,hlog₁,hlog₂⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_actual_both_log_deficits_lt_3_2
