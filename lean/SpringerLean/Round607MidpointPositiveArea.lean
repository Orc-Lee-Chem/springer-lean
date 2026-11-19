import SpringerLean.Round606MidpointOmittedArea

open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem exteriorReciprocalGerm_deriv_disk_energy_pos
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V)
    (hnz : ∀ z ∈ exteriorDisk, V z ≠ 0)
    (hsum : Summable (fun j : ℕ => (j : ℝ) * ‖exteriorReciprocalCoeff V j‖ ^ 2)) :
    0 < Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2) := by
  let f : ℂ → ℝ := fun z => ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2
  have hRa := exteriorReciprocalGerm_analyticOnNhd_unitBall V hV hnz
  have hi : IntegrableOn f (Metric.ball (0 : ℂ) 1) :=
    (analytic_deriv_unitDisk_energy_le (exteriorReciprocalGerm V) hRa hsum).1
  have hd : deriv (exteriorReciprocalGerm V) 0 = 1 := by
    simpa only [exteriorReciprocalCoeff, actualTaylorCoeff, iteratedDeriv_one,
      Nat.factorial_one, Nat.cast_one, div_one] using exteriorReciprocalCoeff_one V hV
  have hc : ContinuousAt (deriv (exteriorReciprocalGerm V)) (conj (0 : ℂ)) := by
    simpa only [map_zero] using (hRa.deriv 0 (by simp)).continuousAt
  have hf : ContinuousAt f 0 :=
    (hc.comp (by fun_prop : ContinuousAt (fun z : ℂ => conj z) 0)).norm.pow 2
  have hfnz : f 0 ≠ 0 := by simp [f,hd]
  have hsupport : Function.support f ∈ 𝓝 (0 : ℂ) := hf.eventually_ne hfnz
  have hm : 0 < volume (Function.support f ∩ Metric.ball (0 : ℂ) 1) :=
    Measure.measure_pos_of_mem_nhds volume (inter_mem hsupport (Metric.ball_mem_nhds _ zero_lt_one))
  have hip : 0 < ∫ z in Metric.ball (0 : ℂ) 1, f z :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun z => sq_nonneg _)) hi).mpr hm
  exact mul_pos (inv_pos.mpr Real.pi_pos) hip

theorem exteriorRootMidpoint_omitted_area_pos
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    0 < actualOmittedMoment (exteriorRootMidpoint H J) 0 := by
  have hV := exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ q hq hs
  have hnz : ∀ z ∈ exteriorDisk, exteriorRootMidpoint H J z ≠ 0 :=
    fun z hz => (exteriorRootMidpoint_recover_left H J q hq hs hz).1
  have hsum := exteriorRootMidpoint_reciprocal_weighted_summable H J hH hJ q hq hs
  have hi := exteriorReciprocalGerm_deriv_disk_energy_pos _ hV hnz hsum
  have hq2 : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  exact lt_of_lt_of_le (mul_pos hq2 hi)
    (exteriorRootMidpoint_reciprocal_energy_le_omitted_area H J hH hJ q hq hs)

theorem exteriorOmitted_exists_midpoint_with_positive_area_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ exteriorOmitted F) (hP : P ∈ exteriorOmitted F) (hAP : A ≠ P) :
    ∃ V : ℂ → ℂ, CenteredExteriorUnivalent V ∧
      (∀ z ∈ exteriorDisk, V z ≠ 0) ∧
      exteriorForwardCoeff V 1 = -(A + P) / 4 ∧
      exteriorReciprocalCoeff V 1 = 1 ∧
      IntegrableOn (fun z : ℂ => ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2)
        (Metric.ball (0 : ℂ) 1) ∧
      0 < actualOmittedMoment V 0 ∧
      (‖P - A‖ / 4) ^ 2 * (Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (exteriorReciprocalGerm V) (conj z)‖ ^ 2)) ≤ actualOmittedMoment V 0 ∧
      actualOmittedMoment V 0 ≤ 1 - ‖A + P‖ ^ 2 / 16 := by
  obtain ⟨H, J, hH, hJ, _, _, hsH, hsJ, hV, hbV, hrec⟩ :=
    exteriorOmitted_exists_root_midpoint F hc A P hA hP hAP
  have hq : (P - A) / 4 ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hAP.symm) (by norm_num)
  have hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * ((P - A) / 4) := by
    intro z hz
    rw [hsH z hz, hsJ z hz]
    ring
  have hnz := fun z hz => (hrec z hz).1
  have hsum := exteriorRootMidpoint_reciprocal_weighted_summable H J hH hJ _ hq hs
  have hI := (analytic_deriv_unitDisk_energy_le _
    (exteriorReciprocalGerm_analyticOnNhd_unitBall _ hV hnz) hsum).1
  refine ⟨exteriorRootMidpoint H J, hV, hnz, hbV, exteriorReciprocalCoeff_one _ hV,
    hI, exteriorRootMidpoint_omitted_area_pos H J hH hJ _ hq hs, ?_, ?_⟩
  · simpa only [norm_div, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] using
      exteriorRootMidpoint_reciprocal_energy_le_omitted_area H J hH hJ _ hq hs
  · have he := actualOmittedMoment_zero_le_first_coeff _ hV
    rw [hbV, norm_div, norm_neg] at he
    norm_num at he
    convert he using 1 <;> ring

end SpringerLean
