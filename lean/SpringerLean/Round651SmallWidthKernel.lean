import SpringerLean.Round650WidthLogRemainder
import SpringerLean.Round620StripLogKernel

namespace SpringerLean
set_option Elab.async false

theorem smallWidth_sqrt_deficit_le
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ (1/5000 : ℝ)) :
    Real.sqrt d ≤ (707107 : ℝ)/50000000 := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg d) (by norm_num)).mp
  rw [Real.sq_sqrt hd0]
  exact hd.trans (by norm_num)

/-- The exact S_r at r=1+0.08 sqrt(d), with the constant retained after
extracting one quarter of log(2/d). -/
theorem smallWidth_kernel_lt
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/5000 : ℝ)) :
    exteriorStripLogKernel (1+(2/25 : ℝ)*Real.sqrt d) <
      Real.log (2/d)/4+(92120 : ℝ)/1000000 := by
  let t := Real.sqrt d
  let r := 1+(2/25 : ℝ)*t
  let q := (r^2+1)/((2/25 : ℝ)*(r+1))
  have ht0 : 0 < t := Real.sqrt_pos.mpr hd0
  have htne : t ≠ 0 := ne_of_gt ht0
  have hr : 1 < r := by dsimp only [r]; linarith
  have hr0 : 0 < r := by linarith
  have hrcap : r ≤ smallWidthRadiusCeiling := by
    have h := smallWidth_sqrt_deficit_le hd0.le hd
    dsimp only [r,smallWidthRadiusCeiling,t]
    linarith
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hden : (2/25 : ℝ)*(r+1) ≠ 0 := ne_of_gt (by positivity)
  have hrden : r^2-1 ≠ 0 := by nlinarith
  have hratio : (r^2+1)/(r^2-1)=q/t := by
    dsimp only [q]
    field_simp [htne,hden,hrden]
    dsimp only [r]
    ring
  have hlogd : Real.log d=2*Real.log t := by
    rw [← Real.sq_sqrt hd0.le,Real.log_pow]
    norm_num [t]
  have hL : Real.log (2/d)=Real.log 2-2*Real.log t := by
    rw [Real.log_div (by norm_num) (ne_of_gt hd0),hlogd]
  have hrem := smallWidth_log_remainder_lt hr.le hrcap
  change Real.log q/2-Real.log 2/4-(r^2)⁻¹ < _ at hrem
  change exteriorStripLogKernel r < _
  rw [exteriorStripLogKernel,hratio,Real.log_div (ne_of_gt hq0) htne,hL]
  linarith

end SpringerLean
