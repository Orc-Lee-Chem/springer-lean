import SpringerLean.Round651SmallWidthKernel
import SpringerLean.Round634RealRootCircleWidth

namespace SpringerLean
set_option Elab.async false

/-- Appendix B.2's exact 0.31914 bound, in its valid deficit range.
This is the explicit scalar width of the actual strip, not a numerical
sample or a bound outside the stated small-deficit interval. -/
theorem smallWidth_exact_width_sq_lt
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/5000 : ℝ)) :
    (exteriorRealRootWidth (2-d) (1+(2/25 : ℝ)*Real.sqrt d))^2 <
      (31914 : ℝ)/100000*d*Real.log (2/d) := by
  let t := Real.sqrt d
  let r := 1+(2/25 : ℝ)*t
  let L := Real.log (2/d)
  let E := 1-(2-d)^2/4
  let p := r-(2-d)/(2*r)
  let Q := (166973 : ℝ)/1000000/Real.sqrt L+
    Real.sqrt (1/4+(92120 : ℝ)/1000000/L)
  have ht0 : 0 < t := Real.sqrt_pos.mpr hd0
  have htne : t ≠ 0 := ne_of_gt ht0
  have htd : t^2=d := Real.sq_sqrt hd0.le
  have hr : 1 < r := by dsimp only [r]; linarith
  have hr0 : 0 < r := by linarith
  have hR0 : 0 ≤ 2-d := by linarith
  have hR2 : 2-d ≤ 2 := by linarith
  have hratio : p/t = ((4 : ℝ)/25+((2/25 : ℝ)^2+1/2)*t)/(1+(2/25 : ℝ)*t) := by
    dsimp only [p]
    rw [← htd]
    dsimp only [r]
    field_simp [htne,show 1+(2/25 : ℝ)*t ≠ 0 by positivity]
    <;> ring
  have hp : p ≤ ((166973 : ℝ)/1000000)*t := by
    have h := smallWidth_first_term_ratio_lt (Real.sqrt_nonneg d)
      (smallWidth_sqrt_deficit_le hd0.le hd)
    rw [← hratio] at h
    exact ((div_lt_iff₀ ht0).mp h).le
  have hLlow : Real.log 10000 ≤ L := by
    have harg : (10000 : ℝ) ≤ 2/d := (le_div_iff₀ hd0).mpr (by linarith)
    exact Real.log_le_log (by norm_num) harg
  have hL0 : 0 < L := lt_of_lt_of_le (by
    have h := smallWidth_log_ten_thousand_gt
    linarith) hLlow
  have hS0 : 0 ≤ exteriorStripLogKernel r := exteriorStripLogKernel_nonneg hr
  have hS := smallWidth_kernel_lt hd0 hd
  have hES : E*exteriorStripLogKernel r ≤ d*(L/4+(92120 : ℝ)/1000000) := by
    have hEd : E ≤ d := by dsimp only [E]; nlinarith [sq_nonneg d]
    exact (mul_le_mul_of_nonneg_right hEd hS0).trans
      (mul_le_mul_of_nonneg_left hS.le hd0.le)
  have hroot := Real.sqrt_le_sqrt hES
  rw [Real.sqrt_mul hd0.le] at hroot
  change Real.sqrt (E*exteriorStripLogKernel r) ≤
    t*Real.sqrt (L/4+(92120 : ℝ)/1000000) at hroot
  have hM : exteriorRealRootWidth (2-d) r ≤
      t*((166973 : ℝ)/1000000+Real.sqrt (L/4+(92120 : ℝ)/1000000)) := by
    change p+Real.sqrt (E*exteriorStripLogKernel r) ≤ _
    have h := add_le_add hp hroot
    nlinarith
  have hfac : L*(1/4+(92120 : ℝ)/1000000/L)=L/4+(92120 : ℝ)/1000000 := by
    field_simp [ne_of_gt hL0]
    <;> ring
  have hrootfac : Real.sqrt (L/4+(92120 : ℝ)/1000000)=
      Real.sqrt L*Real.sqrt (1/4+(92120 : ℝ)/1000000/L) := by
    rw [← hfac,Real.sqrt_mul hL0.le]
  have hnorm : t*((166973 : ℝ)/1000000+Real.sqrt (L/4+(92120 : ℝ)/1000000)) =
      t*Real.sqrt L*Q := by
    rw [hrootfac]
    dsimp only [Q]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hL0)]
    <;> ring
  rw [hnorm] at hM
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hM0 : 0 ≤ exteriorRealRootWidth (2-d) r :=
    exteriorRealRootWidth_nonneg hR0 hR2 hr
  have hsq : (exteriorRealRootWidth (2-d) r)^2 ≤ (t*Real.sqrt L*Q)^2 :=
    (sq_le_sq₀ hM0 (by positivity)).mpr hM
  have hscale : (t*Real.sqrt L*Q)^2=d*L*Q^2 := by
    rw [mul_pow,mul_pow,htd,Real.sq_sqrt hL0.le]
  have hQ := smallWidth_ratio_sq_lt hLlow
  have hlast : d*L*Q^2 < d*L*((31914 : ℝ)/100000) :=
    mul_lt_mul_of_pos_left hQ (mul_pos hd0 hL0)
  change (exteriorRealRootWidth (2-d) r)^2 < _
  rw [hscale] at hsq
  nlinarith

end SpringerLean
