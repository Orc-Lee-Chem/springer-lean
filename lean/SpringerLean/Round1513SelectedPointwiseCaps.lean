import SpringerLean.Round1512ActualFillingPointwiseCap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

open Set
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- Every cap strictly between zero and two is the average of the
centered cosine over a unique-size arc; only existence is used here. -/
theorem exists_flattened_angle_of_radius {R : ℝ}
    (hR0 : 0 < R) (hR2 : R < 2) :
    ∃ h : ℝ, 0 < h ∧ h < Real.pi ∧ R = 2*Real.sin h/h := by
  let g : ℝ → ℝ := fun x => 2*Real.sinc x
  have hπ : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
  have hc : ContinuousOn g (Icc 0 Real.pi) :=
    (continuous_const.mul Real.continuous_sinc).continuousOn
  have hg0 : g 0 = 2 := by simp [g]
  have hgπ : g Real.pi = 0 := by
    simp [g, Real.sinc_of_ne_zero Real.pi_ne_zero]
  have hmem : R ∈ Icc (g Real.pi) (g 0) := by
    rw [hg0, hgπ]
    exact ⟨hR0.le,hR2.le⟩
  obtain ⟨h,hh,hg⟩ := (intermediate_value_Icc' hπ hc) hmem
  have hh0 : 0 < h := by
    rcases hh with ⟨hh0,hhπ⟩
    exact lt_of_le_of_ne hh0 (by
      intro heq
      rw [←heq,hg0] at hg
      linarith)
  have hhπ : h < Real.pi := by
    rcases hh with ⟨_,hhπ⟩
    exact lt_of_le_of_ne hhπ (by
      intro heq
      rw [heq,hgπ] at hg
      linarith)
  refine ⟨h,hh0,hhπ,?_⟩
  calc
    R = 2*(Real.sin h/h) := by simpa [g,Real.sinc_of_ne_zero hh0.ne'] using hg.symm
    _ = 2*Real.sin h/h := by ring

/-- The actual selected Catalan-candidate endpoints now each supply
their own sharpened Poisson cap on every positive real inner radius. -/
theorem exteriorInverseCoeff_candidate_selected_two_pointwise_caps
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
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 2*Real.sin h₁/h₁) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ 2*Real.sin h₂/h₂) ∧
      (∀ {r : ℝ}, 0 < r → r < 1 →
        (conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F (r:ℂ)).re ≤
          flattenedCosinePoissonAtReal h₁ r) ∧
      (∀ {r : ℝ}, 0 < r → r < 1 →
        (conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F (r:ℂ)).re ≤
          flattenedCosinePoissonAtReal h₂ r) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    _hlog₁,_hlog₂,_hW₁,_hW₂,_hmW₁,_hmW₂,
    _hmax₁,_hneg,_hmax₂,hcap₁,hcap₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_global_caps F hc k hk hB hns
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hR₁0 : 0 < ‖P₁‖ := by
    have hm := mul_le_mul_of_nonneg_right hn hd₁.le
    nlinarith
  have hR₂0 : 0 < ‖P₂‖ := by
    have hm := mul_le_mul_of_nonneg_right hn hd₂.le
    nlinarith
  have hR₁2 : ‖P₁‖ < 2 := by linarith
  have hR₂2 : ‖P₂‖ < 2 := by linarith
  obtain ⟨h₁,hh₁0,hh₁π,h₁eq⟩ := exists_flattened_angle_of_radius hR₁0 hR₁2
  obtain ⟨h₂,hh₂0,hh₂π,h₂eq⟩ := exists_flattened_angle_of_radius hR₂0 hR₂2
  have hP₁ne : P₁ ≠ 0 := by
    intro he
    simp [he] at hR₁0
  have hP₂ne : P₂ ≠ 0 := by
    intro he
    simp [he] at hR₂0
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by
    simp [hP₁ne]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by
    simp [hP₂ne]
  have hc₁ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 2*Real.sin h₁/h₁ := by
    simpa only [←h₁eq] using hcap₁
  have hc₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ 2*Real.sin h₂/h₂ := by
    simpa only [←h₂eq] using hcap₂
  refine ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hh₁0,hh₁π,hh₂0,hh₂π,h₁eq,h₂eq,hc₁,hc₂,?_,?_⟩
  · intro r hr0 hr1
    exact actualHarmonic_flattened_pointwise_cap
      F hc _ hunit₁ h₁ hh₁0 hh₁π hc₁ hr0 hr1
  · intro r hr0 hr1
    exact actualHarmonic_flattened_pointwise_cap
      F hc _ hunit₂ h₂ hh₂0 hh₂π hc₂ hr0 hr1

end SpringerLean

#print axioms SpringerLean.exists_flattened_angle_of_radius
#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_pointwise_caps
