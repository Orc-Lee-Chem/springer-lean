import SpringerLean.Round1483FineWidthDiskScale

namespace SpringerLean

/-- Both of the actual selected omitted endpoints now have a full-hull
fine strip whose squared width is less than one third of `dL` and
whose disk-scale width is less than one half. The corresponding strip
inequalities for every hull point are in
`exteriorOmitted_actualEndpoint_fine_strip`. -/
theorem exteriorInverseCoeff_candidate_actual_two_fine_widths
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
        Real.log (2/(2-‖P₂‖)) < 3/2 ∧
      exteriorFineEndpointWidth P₁ <
        (1/3:ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) ∧
      exteriorFineEndpointWidth P₂ <
        (1/3:ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) ∧
      ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P₁ < 1/2 ∧
      ((2*k-2:ℕ):ℝ)*exteriorFineEndpointWidth P₂ < 1/2 := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hlog₁,hlog₂⟩ :=
    exteriorInverseCoeff_candidate_actual_both_log_deficits_lt_3_2
      F hc k hk hB hns
  obtain ⟨hW₁,hmW₁⟩ :=
    exteriorOmitted_actualEndpoint_fine_width_disk_scale
      F hc k hk P₁ hP₁ hd₁ ht₁ hlog₁
  obtain ⟨hW₂,hmW₂⟩ :=
    exteriorOmitted_actualEndpoint_fine_width_disk_scale
      F hc k hk P₂ hP₂ hd₂ ht₂ hlog₂
  exact ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    hlog₁,hlog₂,hW₁,hW₂,hmW₁,hmW₂⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_actual_two_fine_widths
