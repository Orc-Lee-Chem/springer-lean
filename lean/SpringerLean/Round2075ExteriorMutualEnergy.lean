import SpringerLean.Round2074ExteriorPotentialOnOmitted

open Metric Set Filter MeasureTheory Real

namespace SpringerLean

/-- The actual radial law and any probability carried by the omitted
set have integrable mutual logarithmic kernel and mutual energy zero.
The product measure does not charge the diagonal. -/
theorem actualExteriorBoundaryProbability_mutual_log_energy
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : exteriorOmitted F ∈ ae ν) :
    (∀ᵐ p ∂ν.prod (actualExteriorBoundaryProbability F), p.2 ≠ p.1) ∧
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.2 - p.1‖)
      (ν.prod (actualExteriorBoundaryProbability F)) ∧
    (∫ p : ℂ × ℂ, Real.log ‖p.2 - p.1‖ ∂ν.prod (actualExteriorBoundaryProbability F)) = 0 := by
  let μ := actualExteriorBoundaryProbability F
  let L (p : ℂ × ℂ) := Real.log ‖p.2 - p.1‖
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hμ : exteriorOmitted F ∈ ae μ :=
    actualExteriorBoundaryProbability_ae_mem_omitted F hF
      (exteriorOmitted_isCompact F hF).isClosed
  have hm : Measurable L := by unfold L; fun_prop
  have hslice : ∀ᵐ x ∂ν, Integrable (fun z => L (x,z)) μ := by
    filter_upwards [hν] with x hx
    exact (actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF x hx).2.1
  have hzero : ∀ᵐ x ∂ν, ∫ z, L (x,z) ∂μ = 0 := by
    filter_upwards [hν] with x hx
    exact actualExteriorBoundaryProbability_log_potential_on_omitted F hF x hx
  have hdiag : ∀ᵐ p ∂ν.prod μ, p.2 ≠ p.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_snd continuous_fst).isOpen_compl.measurableSet).mpr
    filter_upwards [hν] with x hx
    exact (actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF x hx).1
  have hleft : Integrable (fun x => ∫ z, ‖L (x,z)‖ ∂μ) ν := by
    apply Integrable.mono (integrable_const (2 * Real.log 5))
      hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hν, hslice, hzero] with x hx hi h0
    have hpos : (∫ z, (L (x,z))⁺ ∂μ) ≤ Real.log 5 := by
      have hle : ∀ᵐ z ∂μ, (L (x,z))⁺ ≤ Real.log 5 := by
        filter_upwards [hμ,
          (actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF x hx).1]
          with z hz hne
        have hd : ‖z-x‖ ≤ 5 := (norm_sub_le _ _).trans (by
          linarith [exteriorOmitted_norm_le_two F hF hz, exteriorOmitted_norm_le_two F hF hx])
        apply max_le
        · exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hd
        · exact Real.log_nonneg (by norm_num)
      simpa only [posPart, integral_const, probReal_univ, one_smul] using
        integral_mono_ae hi.pos_part (integrable_const (Real.log 5)) hle
    rw [norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
      norm_of_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))]
    simp only [Real.norm_eq_abs]
    rw [integral_abs_eq_two_mul_integral_posPart_sub_integral hi, h0, sub_zero]
    exact mul_le_mul_of_nonneg_left hpos (by norm_num)
  have hint : Integrable L (ν.prod μ) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨hslice, hleft⟩
  refine ⟨hdiag, hint, ?_⟩
  change (∫ p, L p ∂ν.prod μ) = 0
  rw [integral_prod L hint, integral_congr_ae hzero, integral_zero]

end SpringerLean
