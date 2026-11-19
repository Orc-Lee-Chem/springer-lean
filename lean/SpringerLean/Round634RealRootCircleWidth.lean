import SpringerLean.Round633ActualOddTailBound

namespace SpringerLean
set_option Elab.async false

/-- The elementary first two Laurent modes in the real-endpoint strip.
The factor is nonnegative because 0 <= R <= 2 and r > 1. -/
theorem realRoot_principal_re_abs_le
    {R r : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2) (hr : 1 < r)
    {z : ℂ} (hz : ‖z‖ = r) :
    |(z-(R : ℂ)/2*z⁻¹).re| ≤ r-R/(2*r) := by
  have hr0 : 0 < r := by linarith
  have hr2 : 1 < r^2 := by nlinarith
  have hfac : 0 ≤ 1-R/(2*r^2) := by
    have hp : 0 < 2*r^2 := by positivity
    have hq : R/(2*r^2) ≤ 1 := (div_le_one hp).mpr (by linarith)
    linarith
  have hRe : (z-(R : ℂ)/2*z⁻¹).re = z.re*(1-R/(2*r^2)) := by
    simp only [Complex.sub_re,Complex.mul_re,Complex.div_ofNat_re,
      Complex.ofReal_re,Complex.div_ofNat_im,Complex.ofReal_im,
      zero_div,zero_mul,sub_zero,Complex.inv_re,Complex.normSq_eq_norm_sq,hz]
    ring
  rw [hRe,abs_mul,abs_of_nonneg hfac]
  calc
    |z.re| * (1-R/(2*r^2)) ≤ r*(1-R/(2*r^2)) :=
      mul_le_mul_of_nonneg_right (by simpa only [hz] using Complex.abs_re_le_norm z) hfac
    _ = r-R/(2*r) := by
      field_simp [ne_of_gt hr0]
      <;> ring

noncomputable def exteriorRealRootWidth (R r : ℝ) : ℝ :=
  r-R/(2*r)+Real.sqrt ((1-R^2/4)*exteriorStripLogKernel r)

theorem exteriorRealRootWidth_nonneg
    {R r : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2) (hr : 1 < r) :
    0 ≤ exteriorRealRootWidth R r := by
  have hr0 : 0 < r := by linarith
  have hp : 0 < 2*r := by positivity
  have hq : R/(2*r) ≤ r := (div_le_iff₀ hp).mpr (by nlinarith)
  exact add_nonneg (sub_nonneg.mpr hq) (Real.sqrt_nonneg _)

/-- Explicit logarithmic width on an actual source circle of the odd root. -/
theorem exterior_real_odd_root_circle_re_abs_le
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    (hodd : ∀ z, H (-z) = -H z)
    {R r : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2) (hr : 1 < r)
    (hb : exteriorForwardCoeff H 1 = -(R : ℂ)/2)
    {z : ℂ} (hz : ‖z‖ = r) :
    |(H z).re| ≤ exteriorRealRootWidth R r := by
  have ht := exterior_odd_tail_norm_le H hc hodd hr hz
  have hbN : ‖exteriorForwardCoeff H 1‖^2 = R^2/4 := by
    rw [hb,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0]
    norm_num
    ring
  rw [hbN,hb] at ht
  have hE : H z = (z-(R : ℂ)/2*z⁻¹)+(H z-z+(R : ℂ)/2*z⁻¹) := by ring
  calc
    |(H z).re| = |(z-(R : ℂ)/2*z⁻¹).re+
        (H z-z+(R : ℂ)/2*z⁻¹).re| := by rw [← Complex.add_re,← hE]
    _ ≤ |(z-(R : ℂ)/2*z⁻¹).re|+|(H z-z+(R : ℂ)/2*z⁻¹).re| := abs_add_le _ _
    _ ≤ (r-R/(2*r))+‖H z-z+(R : ℂ)/2*z⁻¹‖ :=
      add_le_add (realRoot_principal_re_abs_le hR0 hR2 hr hz) (Complex.abs_re_le_norm _)
    _ ≤ exteriorRealRootWidth R r := by
      dsimp only [exteriorRealRootWidth]
      exact add_le_add le_rfl (by
        simpa only [neg_div,neg_mul,sub_neg_eq_add] using ht)

end SpringerLean
