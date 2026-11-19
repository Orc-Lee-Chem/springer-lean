import SpringerLean.Round1523FlatModelPeakNonnegative

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The clipped positive-power circle comparison for the actual map
has no extra sign hypothesis: positivity of the model peak is proved. -/
theorem actualHarmonic_inner_positivePower_le_clippedModel_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    Real.circleAverage
      (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r ≤
    Real.circleAverage
      (fun z : ℂ => clippedTangentPower
        (flattenedCosinePoissonAtReal h r) m (2*z.re)) 0 r :=
  actualHarmonic_inner_positivePower_le_clippedModel
    F hc ξ hξ h hh0 hhpi hcap hr0 hr1
      (flattenedCosinePoissonAtReal_nonneg h hh0 hhpi hr0 hr1) hm

/-- The same two selected actual candidate endpoints each yield the
unconditional clipped-power comparison at every inner radius. -/
theorem exteriorInverseCoeff_candidate_selected_two_clipped_inner_moments
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ, ∃ h₁ h₂ : ℝ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < h₁ ∧ h₁ < Real.pi ∧ 0 < h₂ ∧ h₂ < Real.pi ∧
      ‖P₁‖ = 2*Real.sin h₁/h₁ ∧
      ‖P₂‖ = 2*Real.sin h₂/h₂ ∧
      (∀ {r : ℝ}, 0 < r → r < 1 → ∀ {m : ℕ}, 1 ≤ m →
        Real.circleAverage
          (fun z => (max ((conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F z).re) 0)^m) 0 r ≤
        Real.circleAverage
          (fun z : ℂ => clippedTangentPower
            (flattenedCosinePoissonAtReal h₁ r) m (2*z.re)) 0 r) ∧
      (∀ {r : ℝ}, 0 < r → r < 1 → ∀ {m : ℕ}, 1 ≤ m →
        Real.circleAverage
          (fun z => (max ((conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F z).re) 0)^m) 0 r ≤
        Real.circleAverage
          (fun z : ℂ => clippedTangentPower
            (flattenedCosinePoissonAtReal h₂ r) m (2*z.re)) 0 r) := by
  obtain ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hh₁0,hh₁π,hh₂0,hh₂π,
    h₁eq,h₂eq,hcap₁,hcap₂,_hreal₁,_hreal₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_pointwise_caps F hc k hk hB hns
  have hR₁0 : 0 < ‖P₁‖ := by
    rw [h₁eq]
    exact div_pos (mul_pos (by norm_num)
      (Real.sin_pos_of_pos_of_lt_pi hh₁0 hh₁π)) hh₁0
  have hR₂0 : 0 < ‖P₂‖ := by
    rw [h₂eq]
    exact div_pos (mul_pos (by norm_num)
      (Real.sin_pos_of_pos_of_lt_pi hh₂0 hh₂π)) hh₂0
  have hP₁ne : P₁ ≠ 0 := by intro he; simp [he] at hR₁0
  have hP₂ne : P₂ ≠ 0 := by intro he; simp [he] at hR₂0
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by simp [hP₁ne]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by simp [hP₂ne]
  refine ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hh₁0,hh₁π,hh₂0,hh₂π,h₁eq,h₂eq,?_,?_⟩
  · intro r hr0 hr1 m hm
    exact actualHarmonic_inner_positivePower_le_clippedModel_actual
      F hc _ hunit₁ h₁ hh₁0 hh₁π hcap₁ hr0 hr1 hm
  · intro r hr0 hr1 m hm
    exact actualHarmonic_inner_positivePower_le_clippedModel_actual
      F hc _ hunit₂ h₂ hh₂0 hh₂π hcap₂ hr0 hr1 hm

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePower_le_clippedModel_actual
#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_clipped_inner_moments
