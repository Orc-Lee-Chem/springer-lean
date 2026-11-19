import SpringerLean.Round612ReciprocalImage
import SpringerLean.Round611InverseAreaBathtub

open MeasureTheory Filter
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem exteriorReciprocal_deriv_integral_eq_inverse_image
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0)
    (hi : IntegrableOn (fun z : ℂ => ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    IntegrableOn (fun w : ℂ => ‖w‖⁻¹ ^ 4) (V '' exteriorDisk) ∧
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2) =
        ∫ w in V '' exteriorDisk, ‖w‖⁻¹ ^ 4 := by
  let f : ℂ → ℝ := fun z => ‖deriv (exteriorReciprocalGerm V) z‖ ^ 2
  have hip : IntegrableOn f (Metric.ball (0 : ℂ) 1) :=
    (unitDisk_integrable_conj_iff f).mp hi
  have hn : ∀ z : ℂ, 0 ≤ f z := fun z => sq_nonneg _
  have hni : ∀ z : ℂ, 0 ≤ ‖z‖⁻¹ ^ 4 := by intro z; positivity
  have hl := ofReal_integral_eq_lintegral_ofReal hip (Eventually.of_forall hn)
  have he := exteriorReciprocalGerm_lintegral_eq_inverse_image V hV hnz
  have hm : Measurable (fun z : ℂ => ‖z‖⁻¹ ^ 4) := by fun_prop
  have hfin : IntegrableOn (fun z : ℂ => ‖z‖⁻¹ ^ 4) (V '' exteriorDisk) := by
    refine ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hni)).mpr ?_⟩
    rw [← he, ← hl]
    exact ENNReal.ofReal_lt_top
  have hr := ofReal_integral_eq_lintegral_ofReal hfin (Eventually.of_forall hni)
  have hreal := congrArg ENNReal.toReal (hl.trans (he.trans hr.symm))
  rw [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (integral_nonneg hni)] at hreal
  exact ⟨hfin, (unitDisk_integral_conj f).trans hreal⟩

/-- The sharp reciprocal-energy lower bound used in the two-point proof.
The omitted set and reciprocal function are actual objects from the same V. -/
theorem exteriorReciprocal_deriv_energy_ge_inv_omitted_area
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0)
    (hi : IntegrableOn (fun z : ℂ => ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2)
      (Metric.ball (0 : ℂ) 1))
    (ha : 0 < actualOmittedMoment V 0) :
    1 / actualOmittedMoment V 0 ≤ Real.pi⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1, ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2) := by
  let K := exteriorOmitted V
  have hK := exteriorOmitted_isCompact V hV
  have hA : actualOmittedMoment V 0 = volume.real K / Real.pi := by
    simp only [actualOmittedMoment, pow_zero, setIntegral_const, smul_eq_mul, mul_one]
    dsimp only [K]
    ring
  have hvol : volume.real K = Real.pi * actualOmittedMoment V 0 := by
    rw [hA]
    field_simp [Real.pi_ne_zero]
  have hKpos : 0 < volume.real K := by rw [hvol]; exact mul_pos Real.pi_pos ha
  obtain ⟨hf,hchange⟩ := exteriorReciprocal_deriv_integral_eq_inverse_image V hV hnz hi
  have hfK : IntegrableOn (fun z : ℂ => ‖z‖⁻¹ ^ 4) Kᶜ := by
    simpa only [K,exteriorOmitted,compl_compl] using hf
  have hb := planar_inverse_fourth_complement_lower K hK.isClosed.measurableSet
    hK.measure_ne_top hKpos hfK
  have hc : (∫ z in Kᶜ, ‖z‖⁻¹ ^ 4) =
      ∫ z in Metric.ball (0 : ℂ) 1, ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2 := by
    simpa only [K,exteriorOmitted,compl_compl] using hchange.symm
  rw [hc] at hb
  have hnorm : Real.pi⁻¹ * (Real.pi ^ 2 / volume.real K) =
      1 / actualOmittedMoment V 0 := by
    rw [hvol]
    field_simp [Real.pi_ne_zero,ne_of_gt ha]
  have he := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)
  rwa [hnorm] at he

end SpringerLean
