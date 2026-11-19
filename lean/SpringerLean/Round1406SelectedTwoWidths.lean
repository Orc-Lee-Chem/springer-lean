import SpringerLean.Round1405ActualLocalizedWidth

open scoped ComplexConjugate

namespace SpringerLean

/-- The same two selected actual omitted endpoints have localized deficits.
For either positive deficit, the 0.34-width strip holds on the whole
ordinary convex hull. Zero deficit is retained explicitly for rigidity. -/
theorem exteriorOmitted_exists_candidate_two_actual_widths
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧
      P₂ ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P₁‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      0 ≤ (((2*k-1:ℕ):ℝ)*(2-‖P₁‖)) ∧
      (((2*k-1:ℕ):ℝ)*(2-‖P₁‖)) < 1 ∧
      0 ≤ (((2*k-1:ℕ):ℝ)*(2-‖P₂‖)) ∧
      (((2*k-1:ℕ):ℝ)*(2-‖P₂‖)) < 1 ∧
      (∀ P : ℂ, (P=P₁ ∨ P=P₂) → 0 < 2-‖P‖ →
        ∀ w ∈ convexHull ℝ (exteriorOmitted F),
          let ξ : ℂ := P/(‖P‖:ℂ)
          let r : ℝ := 1+Real.sqrt (2-‖P‖)/10
          let W : ℝ := (exteriorRealRootWidth ‖P‖ r)^2
          W < (34/100 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) ∧
          (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) ∧
          ‖w‖^2 ≤ ((conj ξ*w).re-2*W)^2+4*W*‖P‖) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hbig,hmax₁,hneg,hmax₂,hd₁,hd₁lt,hd₂,hd₂lt⟩ :=
    exteriorOmitted_exists_candidate_two_actual_deficits_lt_one F hc k hk hB
  refine ⟨P₁,P₂,hP₁,hP₂,hbig,hmax₁,hneg,hmax₂,
    hd₁,hd₁lt,hd₂,hd₂lt,?_⟩
  intro P hchoice hdpos w hw
  rcases hchoice with rfl | rfl
  · exact exteriorOmitted_actualEndpoint_localized_strip
      F hc k hk P hP₁ hdpos hd₁lt w hw
  · exact exteriorOmitted_actualEndpoint_localized_strip
      F hc k hk P hP₂ hdpos hd₂lt w hw

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_exists_candidate_two_actual_widths
