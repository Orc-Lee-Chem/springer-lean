import SpringerLean.Round650WidthLogRemainder
import SpringerLean.Round620StripLogKernel

namespace SpringerLean
set_option Elab.async false

/-- At the radius `1+sqrt(d)/10`, the logarithmic odd-tail kernel
costs at most one quarter of `log(2/d)` for every deficit below 1/1501.
This closes the interval not covered by the older 1/5000 estimate. -/
theorem mediumWidth_kernel_le
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/1501 : ℝ)) :
    exteriorStripLogKernel (1 + Real.sqrt d / 10) ≤ Real.log (2/d)/4 := by
  let t := Real.sqrt d
  let r := 1 + t / 10
  let R : ℝ := 1 + 1/380
  let q := (r^2+1)/((1/10 : ℝ)*(r+1))
  let Q := (R^2+1)/((1/10 : ℝ)*(R+1))
  have ht0 : 0 < t := Real.sqrt_pos.mpr hd0
  have htne : t ≠ 0 := ne_of_gt ht0
  have htd : t^2 = d := Real.sq_sqrt hd0.le
  have htcap : t ≤ (1/38 : ℝ) := by
    apply (sq_le_sq₀ ht0.le (by norm_num)).mp
    rw [htd]
    exact hd.trans (by norm_num)
  have hr : 1 < r := by dsimp [r]; nlinarith
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by dsimp [R]; norm_num
  have hrcap : r ≤ R := by dsimp [r,R]; linarith
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hden : (1/10 : ℝ)*(r+1) ≠ 0 := ne_of_gt (by positivity)
  have hrden : r^2-1 ≠ 0 := by nlinarith
  have hratio : (r^2+1)/(r^2-1)=q/t := by
    dsimp only [q]
    field_simp [htne,hden,hrden]
    dsimp only [r]
    ring
  have hpoly : (r^2+1)*(R+1) ≤ (R^2+1)*(r+1) := by
    have hid : (R^2+1)*(r+1)-(r^2+1)*(R+1) =
        (R-r)*(R*r+R+r-1) := by ring
    have hp : 0 ≤ (R-r)*(R*r+R+r-1) :=
      mul_nonneg (sub_nonneg.mpr hrcap) (by
        have hprod := mul_nonneg hR0.le hr0.le
        linarith)
    linarith
  have hq : q ≤ Q := by
    have hscaled :
        (r^2+1)*((1/10 : ℝ)*(R+1)) ≤
          (R^2+1)*((1/10 : ℝ)*(r+1)) := by
      have hh := mul_le_mul_of_nonneg_left hpoly
        (by norm_num : (0 : ℝ) ≤ 1/10)
      nlinarith
    apply (div_le_div_iff₀ (by positivity : 0 < (1/10 : ℝ)*(r+1))
      (by positivity : 0 < (1/10 : ℝ)*(R+1))).mpr
    exact hscaled
  have hqsmall : Q/10-1 < (1/500 : ℝ) := by
    norm_num [Q,R]
  have hlogsmall := Real.log_le_sub_one_of_pos
    (div_pos hq0 (by norm_num : (0 : ℝ) < 10))
  rw [Real.log_div (ne_of_gt hq0) (by norm_num)] at hlogsmall
  have hlogten : Real.log (10 : ℝ) = Real.log 5 + Real.log 2 := by
    rw [show (10 : ℝ) = 5*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlogten] at hlogsmall
  have hqdiv : q / 10 ≤ Q / 10 :=
    div_le_div_of_nonneg_right hq (by norm_num)
  have hlogq : Real.log q ≤ Real.log 5 + Real.log 2 + 1/500 := by
    linarith
  have hsq : r^2 ≤ R^2 := (sq_le_sq₀ hr0.le hR0.le).mpr hrcap
  have hinv : (R^2)⁻¹ ≤ (r^2)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < r^2) hsq
  have hRinv : (99/100 : ℝ) < (R^2)⁻¹ := by
    norm_num [R]
  have hcore : Real.log q/2-Real.log 2/4-(r^2)⁻¹ ≤ 0 := by
    linarith [Real.log_five_lt_d9,Real.log_two_lt_d9]
  have hlogd : Real.log d=2*Real.log t := by
    rw [← htd, Real.log_pow]
    norm_num
  have hL : Real.log (2/d)=Real.log 2-2*Real.log t := by
    rw [Real.log_div (by norm_num) (ne_of_gt hd0),hlogd]
  change exteriorStripLogKernel r ≤ _
  rw [exteriorStripLogKernel,hratio,Real.log_div (ne_of_gt hq0) htne,hL]
  linarith

end SpringerLean

#print axioms SpringerLean.mediumWidth_kernel_le
