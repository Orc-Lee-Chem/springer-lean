import SpringerLean.Round1515InnerCircleCappedConvex

open Set
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The same two selected nonslit Catalan-candidate endpoints have
sharpened Poisson peak caps at EVERY angle of EVERY inner circle. -/
theorem exteriorInverseCoeff_candidate_selected_two_circle_peak_caps
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
      (∀ {r : ℝ}, 0 < r → r < 1 → ∀ θ : ℝ,
        (conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F (circleMap 0 r θ)).re ≤
          flattenedCosinePoissonAtReal h₁ r) ∧
      (∀ {r : ℝ}, 0 < r → r < 1 → ∀ θ : ℝ,
        (conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F (circleMap 0 r θ)).re ≤
          flattenedCosinePoissonAtReal h₂ r) := by
  obtain ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hh₁0,hh₁π,hh₂0,hh₂π,
    h₁eq,h₂eq,hcap₁,hcap₂,_hreal₁,_hreal₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_pointwise_caps F hc k hk hB hns
  have hR₁0 : 0 < ‖P₁‖ := by
    rw [h₁eq]
    exact div_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hh₁0 hh₁π)) hh₁0
  have hR₂0 : 0 < ‖P₂‖ := by
    rw [h₂eq]
    exact div_pos (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hh₂0 hh₂π)) hh₂0
  have hP₁ne : P₁ ≠ 0 := by intro he; simp [he] at hR₁0
  have hP₂ne : P₂ ≠ 0 := by intro he; simp [he] at hR₂0
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by simp [hP₁ne]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by simp [hP₂ne]
  refine ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hh₁0,hh₁π,hh₂0,hh₂π,h₁eq,h₂eq,?_,?_⟩
  · intro r hr0 hr1 θ
    exact (actualHarmonic_inner_circle_capped_convex
      F hc _ hunit₁ h₁ hh₁0 hh₁π hcap₁ hr0 hr1).1 θ
  · intro r hr0 hr1 θ
    exact (actualHarmonic_inner_circle_capped_convex
      F hc _ hunit₂ h₂ hh₂0 hh₂π hcap₂ hr0 hr1).1 θ

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_circle_peak_caps
