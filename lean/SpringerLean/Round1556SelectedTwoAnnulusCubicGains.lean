import SpringerLean.Round1555ActualAnnulusCubicGain
import SpringerLean.Round1544SelectedTwoCirclePeakSavings

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Both actually selected omitted endpoints of a nonslit Catalan
candidate admit a strictly positive inner annulus gain. The two annuli
may have different outer radii, and no boundary trace is used. -/
theorem exteriorInverseCoeff_candidate_selected_two_annulus_cubic_gains
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ, ∃ b₁ b₂ : ℝ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 3/20 ∧
      (let m : ℕ := 2*k-2
       let d := 2-‖P₁‖
       let a := 1-Real.sqrt d/16
       a ≤ b₁ ∧ b₁ < 1 ∧
       ((m:ℝ)*d)^3/30 <
         ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
         (∫ z in greenPolarRegion a b₁,
           (max (2*z.re) 0)^m-
             (max ((conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F z).re) 0)^m)) ∧
      (let m : ℕ := 2*k-2
       let d := 2-‖P₂‖
       let a := 1-Real.sqrt d/16
       a ≤ b₂ ∧ b₂ < 1 ∧
       ((m:ℝ)*d)^3/30 <
         ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
         (∫ z in greenPolarRegion a b₂,
           (max (2*z.re) 0)^m-
             (max ((conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F z).re) 0)^m)) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    _hlog₁,_hlog₂,_hW₁,_hW₂,_hmW₁,_hmW₂,
    _hmax₁,_hneg,_hmax₂,hcap₁,hcap₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_global_caps F hc k hk hB hns
  have hmNat : 1500 ≤ 2*k-2 := by omega
  have hmnNat : (2*k-2:ℕ) ≤ 2*k-1 := by omega
  have hmn : ((2*k-2:ℕ):ℝ) ≤ ((2*k-1:ℕ):ℝ) := by
    exact_mod_cast hmnNat
  have hD₁ : ((2*k-2:ℕ):ℝ)*(2-‖P₁‖) ≤ 3/20 := by
    have hp := mul_le_mul_of_nonneg_right hmn hd₁.le
    linarith
  have hD₂ : ((2*k-2:ℕ):ℝ)*(2-‖P₂‖) ≤ 3/20 := by
    have hp := mul_le_mul_of_nonneg_right hmn hd₂.le
    linarith
  have hR₁ : 0 < ‖P₁‖ := by
    have hnNat : 1501 ≤ 2*k-1 := by omega
    have hnR : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
    have hp := mul_le_mul_of_nonneg_right hnR hd₁.le
    nlinarith [ht₁,hp]
  have hR₂ : 0 < ‖P₂‖ := by
    have hnNat : 1501 ≤ 2*k-1 := by omega
    have hnR : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
    have hp := mul_le_mul_of_nonneg_right hnR hd₂.le
    nlinarith [ht₂,hp]
  obtain ⟨h₁,hh₁0,hh₁π,h₁eq⟩ :=
    exists_flattened_angle_of_radius hR₁ (by linarith)
  obtain ⟨h₂,hh₂0,hh₂π,h₂eq⟩ :=
    exists_flattened_angle_of_radius hR₂ (by linarith)
  have hP₁ne : P₁ ≠ 0 := by intro he; simp [he] at hR₁
  have hP₂ne : P₂ ≠ 0 := by intro he; simp [he] at hR₂
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by simp [hP₁ne]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by simp [hP₂ne]
  have hc₁ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 2*Real.sin h₁/h₁ := by
    simpa only [←h₁eq] using hcap₁
  have hc₂ : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₂/(‖P₂‖:ℂ))*w).re ≤ 2*Real.sin h₂/h₂ := by
    simpa only [←h₂eq] using hcap₂
  obtain ⟨b₁,hb₁a,hb₁one,hgain₁⟩ :=
    actualHarmonic_positivePower_exists_annulus_cubic_gain
      F hc _ hunit₁ hh₁0 hh₁π (by linarith [h₁eq]) hd₁ hc₁ hmNat hD₁
  obtain ⟨b₂,hb₂a,hb₂one,hgain₂⟩ :=
    actualHarmonic_positivePower_exists_annulus_cubic_gain
      F hc _ hunit₂ hh₂0 hh₂π (by linarith [h₂eq]) hd₂ hc₂ hmNat hD₂
  exact ⟨P₁,P₂,b₁,b₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    ⟨hb₁a,hb₁one,hgain₁⟩,⟨hb₂a,hb₂one,hgain₂⟩⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_annulus_cubic_gains
