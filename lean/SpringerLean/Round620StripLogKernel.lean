import SpringerLean.Round618OddLogSeries

namespace SpringerLean
set_option Elab.async false

noncomputable def exteriorStripLogKernel (r : ℝ) : ℝ :=
  Real.log ((r^2+1)/(r^2-1))/2-(r^2)⁻¹

/-- The exact nonnegative odd-mode kernel in corrected br:strip. -/
theorem exteriorStripLogKernel_hasSum {r : ℝ} (hr : 1 < r) :
    HasSum (fun k : ℕ => (r⁻¹)^(2*(2*k+3))/(2*k+3 : ℝ))
      (exteriorStripLogKernel r) := by
  have hr0 : 0 < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hr2 : 1 < r^2 := by nlinarith
  have hx0 : 0 ≤ (r^2)⁻¹ := by positivity
  have hx1 : (r^2)⁻¹ < 1 := by
    simpa only [one_div] using (div_lt_one (by positivity : 0 < r^2)).mpr hr2
  have hs := hasSum_odd_log_tail hx0 hx1
  have hratio : (1+(r^2)⁻¹)/(1-(r^2)⁻¹) = (r^2+1)/(r^2-1) := by
    field_simp [hrne,show r^2-1 ≠ 0 by linarith]
    <;> ring
  convert hs using 1
  · funext k
    simp only [inv_pow,pow_mul]
  · simp only [exteriorStripLogKernel,hratio]

theorem exteriorStripLogKernel_nonneg {r : ℝ} (hr : 1 < r) :
    0 ≤ exteriorStripLogKernel r := by
  have hr0 : 0 < r := by linarith
  rw [← (exteriorStripLogKernel_hasSum hr).tsum_eq]
  exact tsum_nonneg (fun _ => by positivity)

end SpringerLean
