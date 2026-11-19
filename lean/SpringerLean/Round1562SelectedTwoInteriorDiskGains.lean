import SpringerLean.Round1561ActualInteriorDiskCubicGain

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The same two selected actual endpoints each give a cubic saving on
a complete compact interior disk. -/
theorem exteriorInverseCoeff_candidate_selected_two_interiorDisk_cubic_gains
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
         (∫ z in greenPolarRegion 0 b₁,
           (max (2*z.re) 0)^m-
             (max ((conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F z).re) 0)^m)) ∧
      (let m : ℕ := 2*k-2
       let d := 2-‖P₂‖
       let a := 1-Real.sqrt d/16
       a ≤ b₂ ∧ b₂ < 1 ∧
       ((m:ℝ)*d)^3/30 <
         ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
         (∫ z in greenPolarRegion 0 b₂,
           (max (2*z.re) 0)^m-
             (max ((conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F z).re) 0)^m)) := by
  obtain ⟨P₁,P₂,b₁,b₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,hgain₁,hgain₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_annulus_cubic_gains
      F hc k hk hB hns
  dsimp only at hgain₁ hgain₂
  obtain ⟨hab₁,hb₁,hann₁⟩ := hgain₁
  obtain ⟨hab₂,hb₂,hann₂⟩ := hgain₂
  have hm : 1500 ≤ 2*k-2 := by omega
  have hmnNat : (2*k-2:ℕ) ≤ 2*k-1 := by omega
  have hmn : ((2*k-2:ℕ):ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hmnNat
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
  have hP₁ne : P₁ ≠ 0 := by intro he; simp [he] at hR₁
  have hP₂ne : P₂ ≠ 0 := by intro he; simp [he] at hR₂
  have hunit₁ : ‖P₁/(‖P₁‖:ℂ)‖=1 := by simp [hP₁ne]
  have hunit₂ : ‖P₂/(‖P₂‖:ℂ)‖=1 := by simp [hP₂ne]
  have ha0₁ : 0 ≤ 1-Real.sqrt (2-‖P₁‖)/16 := by
    have ha1 : 1-Real.sqrt (2-‖P₁‖)/16 ≤ 1 := by
      linarith [Real.sqrt_nonneg (2-‖P₁‖)]
    have hp := thinAnnulus_peak_parameter_bounds hm hd₁ hD₁
      (le_refl _) ha1
    linarith [hp.2.2]
  have ha0₂ : 0 ≤ 1-Real.sqrt (2-‖P₂‖)/16 := by
    have ha1 : 1-Real.sqrt (2-‖P₂‖)/16 ≤ 1 := by
      linarith [Real.sqrt_nonneg (2-‖P₂‖)]
    have hp := thinAnnulus_peak_parameter_bounds hm hd₂ hD₂
      (le_refl _) ha1
    linarith [hp.2.2]
  have hdisk₁ := actualHarmonic_positivePower_annulus_to_disk_gain
    F hc _ hunit₁ ha0₁ hab₁ hb₁ (by omega : 1 ≤ 2*k-2) hann₁
  have hdisk₂ := actualHarmonic_positivePower_annulus_to_disk_gain
    F hc _ hunit₂ ha0₂ hab₂ hb₂ (by omega : 1 ≤ 2*k-2) hann₂
  exact ⟨P₁,P₂,b₁,b₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    ⟨hab₁,hb₁,hdisk₁⟩,⟨hab₂,hb₂,hdisk₂⟩⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_interiorDisk_cubic_gains
