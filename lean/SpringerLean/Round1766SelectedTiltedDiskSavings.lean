import SpringerLean.Round1765ActualTiltedCapAndGain

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Dimensionless full-disk saving for an actual directional positive
power, in the m^(3/2)/2^m normalization of the phase comparison. -/
noncomputable def actualDirectionalPowerSaving
    (F : ℂ → ℂ) (m : ℕ) (v : ℂ) : ℝ :=
  ((m : ℝ)*Real.sqrt (m : ℝ)/(2 : ℝ)^m)*Real.pi⁻¹*
    (∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m -
      (max ((conj v*actualHarmonic F z).re) 0)^m)

/-- The SAME selected actual pair supports arbitrary first-end
directions and every second-end direction within 1/4 of its axis.
All fine-width and radius-maximality data are retained for the
subsequent phase budgets. -/
theorem exteriorInverseCoeff_candidate_selected_two_tilted_disk_savings
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖) < 3/20 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖) < 3/20 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) < 3/2 ∧
      ((2*k-1 : ℕ) : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) < 3/2 ∧
      exteriorFineEndpointWidth P₁ < (1/3 : ℝ)*(2-‖P₁‖)*Real.log (2/(2-‖P₁‖)) ∧
      exteriorFineEndpointWidth P₂ < (1/3 : ℝ)*(2-‖P₂‖)*Real.log (2/(2-‖P₂‖)) ∧
      ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₁ < 1/2 ∧
      ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P₂ < 1/2 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      (∀ v : ℂ, ‖v‖ = 1 →
        ((((2*k-2 : ℕ) : ℝ)*(2-‖P₁‖))^3/30 <
          actualDirectionalPowerSaving F (2*k-2) v)) ∧
      (∀ v : ℂ, ‖v‖ = 1 → ‖v-P₂/(‖P₂‖ : ℂ)‖ ≤ 1/4 →
        ((((2*k-2 : ℕ) : ℝ)*(2-‖P₂‖))^3/30 <
          actualDirectionalPowerSaving F (2*k-2) v)) := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hd₁, hd₂, ht₁, ht₂, hlog₁, hlog₂,
    hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_fine_widths F hc k hk hB hns
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR₁ : 0 < ‖P₁‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd₁.le]
  have hR₂ : 0 < ‖P₂‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd₂.le]
  have hm : 1500 ≤ 2*k-2 := by omega
  have hmn : ((2*k-2 : ℕ) : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2*k-2 ≤ 2*k-1)
  have hD₁ : ((2*k-2 : ℕ) : ℝ)*(2-‖P₁‖) ≤ 3/20 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn hd₁.le]
  have hD₂ : ((2*k-2 : ℕ) : ℝ)*(2-‖P₂‖) ≤ 3/20 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn hd₂.le]
  refine ⟨P₁, P₂, hP₁, hP₂, hd₁, hd₂, ht₁, ht₂, hlog₁, hlog₂,
    hW₁, hW₂, hmW₁, hmW₂, hmax₁, hneg, hmax₂, ?_, ?_⟩
  · intro v hv
    have hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F), (conj v*w).re ≤ ‖P₁‖ := by
      intro w hw
      calc
        _ ≤ ‖conj v*w‖ := Complex.re_le_norm _
        _ = ‖w‖ := by rw [norm_mul, Complex.norm_conj, hv, one_mul]
        _ ≤ ‖P₁‖ := hmax₁ w hw
    exact actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius F hc v hv
      ‖P₁‖ hR₁ (by linarith) hm hD₁ hcap
  · intro v hv hclose
    have hcap := exteriorOmitted_actual_selected_second_tilted_cap F hc k hk P₁ P₂
      hP₁ hd₁ ht₁ hd₂ ht₂ hmW₁ hneg hmax₂ v hv hclose
    exact actualHarmonic_positivePower_unitDisk_cubic_gain_of_radius F hc v hv
      ‖P₂‖ hR₂ (by linarith) hm hD₂ hcap

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_tilted_disk_savings
