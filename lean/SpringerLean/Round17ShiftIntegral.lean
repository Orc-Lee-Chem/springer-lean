import SpringerLean.Round17ShiftRemainder
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set

namespace SpringerLean

/-- Joint integrability of the weighted curvature in the shift remainder. -/
theorem verticalShiftCurvature_integrable_prod (c : ℝ) :
    Integrable (fun p : ℝ × ℝ => (c - p.1) * verticalBaseCurvature (p.2 - p.1))
      ((volume.restrict (uIoc (0 : ℝ) c)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (uIoc (0 : ℝ) c)
  haveI : IsFiniteMeasure μ := by
    by_cases h : 0 ≤ c
    · simpa [μ, uIoc_of_le h] using Real.isFiniteMeasure_restrict_Ioc 0 c
    · have h' : c ≤ 0 := le_of_not_ge h
      simpa [μ, uIoc_of_ge h'] using Real.isFiniteMeasure_restrict_Ioc c 0
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (c - p.1) * verticalBaseCurvature (p.2 - p.1))
      (μ.prod volume) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        (c - p.1) * verticalBaseCurvature (p.2 - p.1)) :=
      (continuous_const.sub continuous_fst).mul
        (verticalBaseCurvature_continuous.comp (continuous_snd.sub continuous_fst))
    exact h.aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · filter_upwards with t
    exact (verticalBaseCurvature_integrable.comp_sub_right t).const_mul (c - t)
  · let K : ℝ := ∫ y : ℝ, ‖verticalBaseCurvature y‖
    have hnorm (t : ℝ) :
        (∫ y : ℝ, ‖(c - t) * verticalBaseCurvature (y - t)‖) = |c - t| * K := by
      simp only [norm_mul, Real.norm_eq_abs, integral_const_mul]
      exact congrArg (fun x : ℝ => |c - t| * x)
        (integral_sub_right_eq_self (μ := volume)
          (fun y : ℝ => ‖verticalBaseCurvature y‖) t)
    simp_rw [hnorm]
    have hcont : Continuous (fun t : ℝ => |c - t| * K) :=
      ((continuous_const.sub continuous_id).abs).mul continuous_const
    exact (hcont.continuousOn.integrableOn_compact isCompact_uIcc).mono_set
      uIoc_subset_uIcc

/-- The correction for imaginary translation is integrable on the full vertical line. -/
theorem verticalShiftRemainder_integrable (c : ℝ) :
    Integrable (verticalShiftRemainder c) := by
  have hp := verticalShiftCurvature_integrable_prod c
  have hi : Integrable (fun y : ℝ => ∫ t : ℝ in (0 : ℝ)..c,
      (c - t) * verticalBaseCurvature (y - t)) := by
    have h := hp.integral_prod_right
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul]
    exact h.const_mul (if (0 : ℝ) ≤ c then 1 else -1 : ℝ)
  convert hi using 1
  funext y
  exact verticalShiftRemainder_eq_intervalIntegral c y

/-- The imaginary-translation correction has zero full-line integral. -/
theorem verticalShiftRemainder_integral_zero (c : ℝ) :
    (∫ y : ℝ, verticalShiftRemainder c y) = 0 := by
  have hp := verticalShiftCurvature_integrable_prod c
  rw [show (fun y : ℝ => verticalShiftRemainder c y) =
      (fun y => ∫ t : ℝ in (0 : ℝ)..c,
        (c - t) * verticalBaseCurvature (y - t)) from
        funext (verticalShiftRemainder_eq_intervalIntegral c)]
  rw [← intervalIntegral_integral_swap hp]
  have hinner (t : ℝ) :
      (∫ y : ℝ, (c - t) * verticalBaseCurvature (y - t)) = 0 := by
    rw [integral_const_mul, verticalBaseCurvature_shift_integral_zero, mul_zero]
  simp_rw [hinner]
  simp

/-- A uniform L¹ estimate for the shift correction. The right-hand side
is finite and depends only on the imaginary displacement. -/
theorem verticalShiftRemainder_abs_integral_le (c : ℝ) :
    (∫ y : ℝ, |verticalShiftRemainder c y|) ≤
      (∫ t : ℝ in uIoc (0 : ℝ) c, |c - t|) *
        (∫ y : ℝ, ‖verticalBaseCurvature y‖) := by
  let μ : Measure ℝ := volume.restrict (uIoc (0 : ℝ) c)
  have hp := verticalShiftCurvature_integrable_prod c
  have hinner : Integrable (fun y : ℝ => ∫ t : ℝ in uIoc (0 : ℝ) c,
      ‖(c - t) * verticalBaseCurvature (y - t)‖) := by
    simpa only [μ] using hp.norm.integral_prod_right
  have hpoint (y : ℝ) :
      |verticalShiftRemainder c y| ≤
        ∫ t : ℝ in uIoc (0 : ℝ) c,
          ‖(c - t) * verticalBaseCurvature (y - t)‖ := by
    rw [verticalShiftRemainder_eq_intervalIntegral]
    simpa only [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm_uIoc
        (a := (0 : ℝ)) (b := c)
        (f := fun t : ℝ => (c - t) * verticalBaseCurvature (y - t)))
  have hle := integral_mono (verticalShiftRemainder_integrable c).abs
    hinner hpoint
  have hswap :
      (∫ y : ℝ, ∫ t : ℝ in uIoc (0 : ℝ) c,
        ‖(c - t) * verticalBaseCurvature (y - t)‖) =
      ∫ t : ℝ in uIoc (0 : ℝ) c,
        (∫ y : ℝ, ‖(c - t) * verticalBaseCurvature (y - t)‖) := by
    have h := integral_integral_swap
      (f := fun t y : ℝ => ‖(c - t) * verticalBaseCurvature (y - t)‖)
      (μ := μ) (ν := volume) hp.norm
    simpa only [μ] using h.symm
  rw [hswap] at hle
  have hnorm (t : ℝ) :
      (∫ y : ℝ, ‖(c - t) * verticalBaseCurvature (y - t)‖) =
        |c - t| * (∫ y : ℝ, ‖verticalBaseCurvature y‖) := by
    simp only [norm_mul, Real.norm_eq_abs, integral_const_mul]
    exact congrArg (fun x : ℝ => |c - t| * x)
      (integral_sub_right_eq_self (μ := volume)
        (fun y : ℝ => ‖verticalBaseCurvature y‖) t)
  simp_rw [hnorm] at hle
  simpa only [integral_mul_const] using hle

/-- An elementary bound on the shift-parameter interval. -/
theorem verticalShiftParameter_abs_integral_le (c : ℝ) :
    (∫ t : ℝ in uIoc (0 : ℝ) c, |c - t|) ≤ c ^ 2 := by
  have hcont : Continuous (fun t : ℝ => |c - t|) :=
    (continuous_const.sub continuous_id).abs
  have hi : IntegrableOn (fun t : ℝ => |c - t|) (uIoc 0 c) :=
    (hcont.continuousOn.integrableOn_compact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hbound (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) c) : |c - t| ≤ |c| := by
    rcases le_total 0 c with hc | hc
    · rw [uIoc_of_le hc] at ht
      rw [abs_of_nonneg hc, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [ht.1]
    · rw [uIoc_of_ge hc] at ht
      rw [abs_of_nonpos hc, abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
      linarith [ht.2]
  have hm := setIntegral_mono_on hi
    (integrableOn_const (s := uIoc (0 : ℝ) c)
      (hs := by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top))
    measurableSet_uIoc hbound
  have hconst : (∫ _t : ℝ in uIoc (0 : ℝ) c, |c|) = c ^ 2 := by
    rw [setIntegral_const, measureReal_def, Real.volume_uIoc]
    simp [abs_nonneg]
    ring
  rwa [hconst] at hm

theorem verticalShiftRemainder_abs_integral_le_sq (c : ℝ) :
    (∫ y : ℝ, |verticalShiftRemainder c y|) ≤
      c ^ 2 * (∫ y : ℝ, ‖verticalBaseCurvature y‖) := by
  have hk : 0 ≤ (∫ y : ℝ, ‖verticalBaseCurvature y‖) :=
    integral_nonneg (fun y => norm_nonneg _)
  exact (verticalShiftRemainder_abs_integral_le c).trans
    (mul_le_mul_of_nonneg_right (verticalShiftParameter_abs_integral_le c) hk)

end SpringerLean
