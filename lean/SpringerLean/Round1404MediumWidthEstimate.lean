import SpringerLean.Round1403MediumWidthKernel
import SpringerLean.Round634RealRootCircleWidth

namespace SpringerLean
set_option Elab.async false

/-- The new radius 1+sqrt(d)/10 gives the 0.34 width through the whole
large-order localization range. -/
theorem mediumWidth_exact_width_sq_lt
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ (1/1501 : ℝ)) :
    (exteriorRealRootWidth (2-d) (1+Real.sqrt d/10))^2 <
      (34/100 : ℝ)*d*Real.log (2/d) := by
  let t := Real.sqrt d
  let r := 1 + t/10
  let L := Real.log (2/d)
  let E := 1-(2-d)^2/4
  let p := r-(2-d)/(2*r)
  let K := exteriorStripLogKernel r
  have ht0 : 0 < t := Real.sqrt_pos.mpr hd0
  have htd : t^2=d := Real.sq_sqrt hd0.le
  have htcap : t ≤ (1/38 : ℝ) := by
    apply (sq_le_sq₀ ht0.le (by norm_num)).mp
    rw [htd]
    exact hd.trans (by norm_num)
  have hr : 1 < r := by dsimp [r]; nlinarith
  have hr0 : 0 < r := by linarith
  have hR0 : 0 ≤ 2-d := by linarith
  have hR2 : 2-d ≤ 2 := by linarith
  have hLarg : (2048 : ℝ) ≤ 2/d := by
    apply (le_div_iff₀ hd0).mpr
    linarith
  have hLlow : 11*Real.log 2 ≤ L := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2048) hLarg
    rw [show (2048 : ℝ)=2^11 by norm_num, Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hL : (15/2 : ℝ) < L := by
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  have hrootL : (27/10 : ℝ) ≤ Real.sqrt L := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg L)).mp
    rw [Real.sq_sqrt hL0.le]
    linarith
  have hratio : p/t = ((1/5 : ℝ)+(51/100)*t)/(1+t/10) := by
    dsimp only [p]
    rw [← htd]
    dsimp only [r]
    field_simp [ne_of_gt ht0, show 1+t/10 ≠ 0 by positivity]
    ring
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*r)).mpr
    dsimp [r]
    nlinarith [sq_nonneg t]
  have hp : p ≤ (11/50 : ℝ)*t := by
    have hrat : p/t ≤ (11/50 : ℝ) := by
      rw [hratio]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+t/10)).mpr
      nlinarith
    exact (div_le_iff₀ ht0).mp hrat
  have hK0 : 0 ≤ K := exteriorStripLogKernel_nonneg hr
  have hK : K ≤ L/4 := mediumWidth_kernel_le hd0 hd
  have hE0 : 0 ≤ E := by dsimp [E]; nlinarith
  have hEd : E ≤ d := by dsimp [E]; nlinarith [sq_nonneg d]
  have hES : E*K ≤ d*(L/4) := by
    exact (mul_le_mul_of_nonneg_right hEd hK0).trans
      (mul_le_mul_of_nonneg_left hK hd0.le)
  have htail : Real.sqrt (E*K) ≤ t*Real.sqrt L/2 := by
    have harg0 : 0 ≤ E*K := mul_nonneg hE0 hK0
    have hsquare := Real.sq_sqrt harg0
    have htarget : (t*Real.sqrt L/2)^2 = d*(L/4) := by
      calc
        _ = t^2*(Real.sqrt L)^2/4 := by ring
        _ = d*(L/4) := by rw [htd,Real.sq_sqrt hL0.le]; ring
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [hsquare,htarget]
    exact hES
  have hpScale : (11/50 : ℝ)*t ≤ (11/135 : ℝ)*t*Real.sqrt L := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ t by positivity)
      (sub_nonneg.mpr hrootL)]
  have hW : exteriorRealRootWidth (2-d) r ≤
      ((11/135 : ℝ)+1/2)*t*Real.sqrt L := by
    change p + Real.sqrt (E*K) ≤ _
    nlinarith [hp,hpScale,htail]
  have hW0 : 0 ≤ exteriorRealRootWidth (2-d) r :=
    exteriorRealRootWidth_nonneg hR0 hR2 hr
  have hQ0 : 0 ≤ ((11/135 : ℝ)+1/2)*t*Real.sqrt L := by positivity
  have hsq := (sq_le_sq₀ hW0 hQ0).mpr hW
  have hscale : (((11/135 : ℝ)+1/2)*t*Real.sqrt L)^2 =
      (((11/135 : ℝ)+1/2)^2)*d*L := by
    rw [mul_pow,mul_pow,htd,Real.sq_sqrt hL0.le]
  have hcoef : (((11/135 : ℝ)+1/2)^2) < 34/100 := by norm_num
  have hprod : 0 < d*L := mul_pos hd0 hL0
  change (exteriorRealRootWidth (2-d) r)^2 < _
  rw [hscale] at hsq
  nlinarith

end SpringerLean

#print axioms SpringerLean.mediumWidth_exact_width_sq_lt
