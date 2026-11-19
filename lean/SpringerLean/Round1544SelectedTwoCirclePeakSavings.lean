import SpringerLean.Round1543ActualCirclePeakSaving

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The SAME selected actual omitted endpoints have localized deficits,
their own flattened cap parameters, and the quantitative circle saving.
The positive-part powers are on the unhalved projection scale. -/
theorem exteriorInverseCoeff_candidate_selected_two_circle_peak_savings
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ, ∃ h₁ h₂ : ℝ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 3/20 ∧
      0 < h₁ ∧ h₁ < Real.pi ∧ 0 < h₂ ∧ h₂ < Real.pi ∧
      ‖P₁‖=2*Real.sin h₁/h₁ ∧
      ‖P₂‖=2*Real.sin h₂/h₂ ∧
      (∀ {r : ℝ}, 0 < r → 1-Real.sqrt (2-‖P₁‖)/3 ≤ r →
        r < 1 → ∀ {m : ℕ}, 2 ≤ m →
        let v := (2-‖P₁‖)-(3/2:ℝ)*(1-r)*Real.sqrt (2-‖P₁‖)
        (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
          (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
        Real.circleAverage (fun z : ℂ => (max (2*z.re) 0)^m) 0 r -
        Real.circleAverage
          (fun z => (max ((conj (P₁/(‖P₁‖:ℂ))*actualHarmonic F z).re) 0)^m)
          0 r) ∧
      (∀ {r : ℝ}, 0 < r → 1-Real.sqrt (2-‖P₂‖)/3 ≤ r →
        r < 1 → ∀ {m : ℕ}, 2 ≤ m →
        let v := (2-‖P₂‖)-(3/2:ℝ)*(1-r)*Real.sqrt (2-‖P₂‖)
        (4/(15*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*
          (2*r-v)^(m-2)*v^2*Real.sqrt v ≤
        Real.circleAverage (fun z : ℂ => (max (2*z.re) 0)^m) 0 r -
        Real.circleAverage
          (fun z => (max ((conj (P₂/(‖P₂‖:ℂ))*actualHarmonic F z).re) 0)^m)
          0 r) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    _hlog₁,_hlog₂,_hW₁,_hW₂,_hmW₁,_hmW₂,
    _hmax₁,_hneg,_hmax₂,hcap₁,hcap₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_global_caps F hc k hk hB hns
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501:ℝ) ≤ ((2*k-1:ℕ):ℝ) := by exact_mod_cast hnNat
  have hn0 : (0:ℝ) < ((2*k-1:ℕ):ℝ) := by linarith
  have hsmall₁ : 2-‖P₁‖ ≤ (1/1500:ℝ) := by
    have hp := mul_nonneg (sub_nonneg.mpr hn) hd₁.le
    nlinarith [ht₁,hp]
  have hsmall₂ : 2-‖P₂‖ ≤ (1/1500:ℝ) := by
    have hp := mul_nonneg (sub_nonneg.mpr hn) hd₂.le
    nlinarith [ht₂,hp]
  have hR₁ : 0 < ‖P₁‖ := by linarith
  have hR₂ : 0 < ‖P₂‖ := by linarith
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
  refine ⟨P₁,P₂,h₁,h₂,hP₁,hP₂,hd₁,hd₂,ht₁,ht₂,
    hh₁0,hh₁π,hh₂0,hh₂π,h₁eq,h₂eq,?_,?_⟩
  · intro r hr0 hrband hr1 m hm
    exact actualHarmonic_inner_positivePower_peak_saving
      F hc _ hunit₁ hh₁0 hh₁π (by linarith [h₁eq]) hd₁ hsmall₁
        hc₁ hr0 hrband hr1 hm
  · intro r hr0 hrband hr1 m hm
    exact actualHarmonic_inner_positivePower_peak_saving
      F hc _ hunit₂ hh₂0 hh₂π (by linarith [h₂eq]) hd₂ hsmall₂
        hc₂ hr0 hrband hr1 hm

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_circle_peak_savings
