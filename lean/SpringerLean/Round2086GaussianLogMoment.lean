import SpringerLean.Round2085GaussianPolynomialProjection
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped Topology

namespace SpringerLean

private theorem gaussianReal_standard_integrable_log :
    Integrable Real.log (gaussianReal 0 1) := by
  let J := Icc (-1 : ℝ) 1
  have hJ : MeasurableSet J := measurableSet_Icc
  have hvol : IntegrableOn Real.log J := by
    unfold J
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num) (by norm_num)).mp
      intervalIntegral.intervalIntegrable_log'
  have hnear : IntegrableOn Real.log J (gaussianReal 0 1) := by
    rw [IntegrableOn, gaussianReal_of_var_ne_zero 0 one_ne_zero,
      restrict_withDensity hJ]
    apply (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    let M := (Real.sqrt (2 * Real.pi))⁻¹
    apply Integrable.mono (hvol.const_mul M)
    · exact ((measurable_gaussianPDF 0 1).ennreal_toReal.smul Real.measurable_log).aestronglyMeasurable
    · filter_upwards with x
      have hpdf : gaussianPDFReal 0 1 x ≤ M := by
        simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, M]
        exact mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg x)) (by norm_num)))
      simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x),
        smul_eq_mul, norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x), abs_of_nonneg (by positivity : 0 ≤ M)]
      exact mul_le_mul_of_nonneg_right hpdf (abs_nonneg _)
  have hfar : IntegrableOn Real.log Jᶜ (gaussianReal 0 1) := by
    have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_id
    apply Integrable.mono hi.restrict Real.measurable_log.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hJ.compl] with x hx
    have ha : 1 ≤ |x| := by
      by_contra! hc
      exact hx (abs_le.mp hc.le)
    have hpos : 0 < |x| := zero_lt_one.trans_le ha
    rw [Real.norm_eq_abs, ← Real.log_abs x, abs_of_nonneg (Real.log_nonneg ha), Real.norm_eq_abs]
    linarith [Real.log_le_sub_one_of_pos hpos]
  have h := hnear.union hfar
  rwa [union_compl_self, integrableOn_univ] at h

theorem stdGaussian_complex_ae_re_ne_zero :
    ∀ᵐ z ∂stdGaussian ℂ, z.re ≠ 0 := by
  have hgauss : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hr : ∀ᵐ x ∂gaussianReal 0 1, x ≠ 0 := by simp [ae_iff]
  rw [← stdGaussian_complex_map_re] at hr
  exact (ae_map_iff Complex.continuous_re.measurable.aemeasurable
    (measurableSet_singleton (0 : ℝ)).compl).mp hr

theorem stdGaussian_complex_ae_ne_zero : ∀ᵐ z ∂stdGaussian ℂ, z ≠ 0 :=
  stdGaussian_complex_ae_re_ne_zero.mono (fun z hz he => hz (by simp [he]))

theorem stdGaussian_complex_integrable_log_norm :
    Integrable (fun z : ℂ => Real.log ‖z‖) (stdGaussian ℂ) := by
  let γ := stdGaussian ℂ
  have hre : Integrable (fun z : ℂ => Real.log z.re) γ := by
    have hint := gaussianReal_standard_integrable_log
    rw [← stdGaussian_complex_map_re] at hint
    exact (integrable_map_measure Real.measurable_log.aestronglyMeasurable
      Complex.continuous_re.measurable.aemeasurable).mp hint
  have hn : Integrable (fun z : ℂ => ‖z‖) γ :=
    (show Integrable (fun z : ℂ => z) γ from IsGaussian.integrable_id).norm
  apply Integrable.mono' (hn.add hre.norm)
    (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable
  filter_upwards [stdGaussian_complex_ae_re_ne_zero] with z hz
  have hzr : 0 < |z.re| := abs_pos.mpr hz
  have hle : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzpos : 0 < ‖z‖ := hzr.trans_le hle
  change ‖Real.log ‖z‖‖ ≤ ‖z‖ + ‖Real.log z.re‖
  by_cases h : ‖z‖ ≤ 1
  · have hlo := Real.log_le_log hzr hle
    rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hzpos.le h),
      Real.norm_eq_abs, ← Real.log_abs z.re]
    exact (neg_le_neg hlo).trans (by linarith [neg_abs_le (Real.log |z.re|)])
  · have h' : 1 ≤ ‖z‖ := (lt_of_not_ge h).le
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h')]
    linarith [Real.log_le_sub_one_of_pos hzpos, norm_nonneg (Real.log z.re)]

end SpringerLean
