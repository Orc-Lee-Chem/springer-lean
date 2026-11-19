import SpringerLean.Round605ReciprocalDirichletBudget
import SpringerLean.Round11Energy

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem actualHarmonicMoment_zero (F : ℂ → ℂ) : actualHarmonicMoment F 0 = 1 := by
  simp only [actualHarmonicMoment, pow_zero, setIntegral_const, smul_eq_mul, mul_one]
  rw [measureReal_def, Complex.volume_ball]
  simp [Real.pi_pos.le, Real.pi_ne_zero]

theorem actualOmittedMoment_zero_le_first_coeff
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V) :
    actualOmittedMoment V 0 ≤ 1 - ‖exteriorForwardCoeff V 1‖ ^ 2 := by
  have he := exteriorInverseCoeff_odd_norm_sq_le_moment_product V hV (k := 1) (by omega)
  simp only [Nat.reduceMul, Nat.reduceSub, actualHarmonicMoment_zero, one_mul,
    exteriorInverseCoeff_one_eq_forwardCoeff_one V hV] at he
  linarith

theorem exteriorRootMidpoint_reciprocal_energy_le_omitted_area
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    ‖q‖ ^ 2 * (Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv (exteriorReciprocalGerm (exteriorRootMidpoint H J)) (conj z)‖ ^ 2)) ≤
        actualOmittedMoment (exteriorRootMidpoint H J) 0 := by
  have he := exteriorRootMidpoint_dirichlet_budget H J hH hJ q hq hs
  have hV := exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ q hq hs
  have ha := actualHarmonic_deriv_weighted_eq_moment_sub
    (exteriorRootMidpoint H J) hV (k := 1) (by omega)
  simp only [Nat.reduceMul, Nat.reduceSub, pow_zero, one_mul,
    actualHarmonicMoment_zero] at ha
  rw [ha] at he
  linarith

/-- Both sides of the corrected midpoint-area argument, now for two actual
omitted points of the original F. The remaining lower bound on the reciprocal
integral is deliberately not assumed or asserted here. -/
theorem exteriorOmitted_exists_midpoint_with_actual_area_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ exteriorOmitted F) (hP : P ∈ exteriorOmitted F) (hAP : A ≠ P) :
    ∃ V : ℂ → ℂ, CenteredExteriorUnivalent V ∧
      (∀ z ∈ exteriorDisk, V z ≠ 0) ∧
      exteriorForwardCoeff V 1 = -(A + P) / 4 ∧
      exteriorReciprocalCoeff V 1 = 1 ∧
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
  refine ⟨exteriorRootMidpoint H J, hV, fun z hz => (hrec z hz).1, hbV,
    exteriorReciprocalCoeff_one _ hV, ?_, ?_⟩
  · simpa only [norm_div, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] using
      exteriorRootMidpoint_reciprocal_energy_le_omitted_area H J hH hJ _ hq hs
  · have he := actualOmittedMoment_zero_le_first_coeff _ hV
    rw [hbV, norm_div, norm_neg] at he
    norm_num at he
    convert he using 1 <;> ring

end SpringerLean
