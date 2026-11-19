import SpringerLean.Round571Order15RingCheckPureG06
import SpringerLean.Round33CenteredArc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Set

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- Continuous odd boundary primitive for the capped model. This asserts
no unproved comparison with an actual F. -/
noncomputable def cappedAngularTopBoundary (q : ℝ) (z : ℂ) : ℝ :=
  min (2*q*Real.arccos z.re) (max (4*z.im) 0) -
    min (2*q*Real.arccos z.re) (max (-4*z.im) 0)

theorem cappedAngularTopBoundary_continuous (q : ℝ) :
    Continuous (cappedAngularTopBoundary q) := by
  unfold cappedAngularTopBoundary
  fun_prop

theorem cappedAngularTopBoundary_conj (q : ℝ) (z : ℂ) :
    cappedAngularTopBoundary q (star z) = -cappedAngularTopBoundary q z := by
  simp only [cappedAngularTopBoundary, Complex.star_def, Complex.conj_re,
    Complex.conj_im, mul_neg, neg_mul, neg_neg]
  ring

theorem cappedAngularTopBoundary_real {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    cappedAngularTopBoundary q (x : ℂ) = 0 := by
  simp only [cappedAngularTopBoundary, Complex.ofReal_im, mul_zero,
    max_self, sub_self]

/-- No discontinuous argument/sign function is needed at the endpoints. -/
theorem cappedAngularTopBoundary_upper_circle {q : ℝ} (hq : 0 ≤ q)
    {h : ℝ} (hh0 : 0 ≤ h) (hhpi : h ≤ Real.pi) :
    cappedAngularTopBoundary q (circleMap 0 1 h) = min (2*q*h) (4*Real.sin h) := by
  have hs : 0 ≤ Real.sin h := Real.sin_nonneg_of_mem_Icc ⟨hh0,hhpi⟩
  have hqh : 0 ≤ 2*q*h := by positivity
  simp only [cappedAngularTopBoundary, circleMap_zero_re, circleMap_zero_im, one_mul,
    Real.arccos_cos hh0 hhpi]
  rw [max_eq_left (by positivity : 0 ≤ 4*Real.sin h),
    max_eq_right (by nlinarith : -4*Real.sin h ≤ 0), min_eq_right hqh, sub_zero]

theorem cappedAngularTopBoundary_abs_le {q : ℝ} (hq : 0 ≤ q) (z : ℂ) :
    |cappedAngularTopBoundary q z| ≤ 4*|z.im| := by
  have ha : 0 ≤ 2*q*Real.arccos z.re :=
    mul_nonneg (mul_nonneg (by norm_num) hq) (Real.arccos_nonneg z.re)
  by_cases hz : 0 ≤ z.im
  · have hb : 0 ≤ min (2*q*Real.arccos z.re) (4*z.im) := le_min ha (by positivity)
    have hc := min_le_right (2*q*Real.arccos z.re) (4*z.im)
    simp only [cappedAngularTopBoundary,
      max_eq_left (by positivity : 0 ≤ 4*z.im),
      max_eq_right (by nlinarith : -4*z.im ≤ 0), min_eq_right ha, sub_zero,
      abs_of_nonneg hb, abs_of_nonneg hz]
    exact hc
  · have hzn : z.im ≤ 0 := le_of_lt (lt_of_not_ge hz)
    have hb : 0 ≤ min (2*q*Real.arccos z.re) (-4*z.im) := le_min ha (by nlinarith)
    have hc := min_le_right (2*q*Real.arccos z.re) (-4*z.im)
    simp only [cappedAngularTopBoundary,
      max_eq_right (by nlinarith : 4*z.im ≤ 0),
      max_eq_left (by nlinarith : 0 ≤ -4*z.im), min_eq_right ha, zero_sub,
      abs_neg, abs_of_nonneg hb, abs_of_nonpos hzn]
    nlinarith

end SpringerLean

#print axioms SpringerLean.cappedAngularTopBoundary_continuous
#print axioms SpringerLean.cappedAngularTopBoundary_conj
#print axioms SpringerLean.cappedAngularTopBoundary_upper_circle
#print axioms SpringerLean.cappedAngularTopBoundary_abs_le
