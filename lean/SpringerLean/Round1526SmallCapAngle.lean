import SpringerLean.Round1525ClippedPowerPointwiseGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SpringerLean
set_option maxHeartbeats 20000

/-- The cap arc corresponding to a deficit at most 1/1500 is shorter
than one half radian. -/
theorem small_flattened_arc_lt_half
    {h d : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d = 2-2*Real.sin h/h)
    (hdle : d ≤ 1/1500) : h < 1/2 := by
  by_contra hbad
  have hhalf : (1/2:ℝ) ≤ h := le_of_not_gt hbad
  have hs := sine_arc_ratio_le (u := 1/2) (v := h)
    (by norm_num) hhalf hhpi.le
  have hsinHalf : Real.sin (1/2:ℝ) ≤ 23015/48000 := by
    have hb := Real.sin_bound (x := (1/2:ℝ)) (by norm_num)
    have hu := (abs_le.mp hb).2
    norm_num at hu
    linarith only [hu]
  have hdexpr : d*h=2*h-2*Real.sin h := by
    rw [hd]
    field_simp
  have hdmax : d*h ≤ (1/1500:ℝ)*h :=
    mul_le_mul_of_nonneg_right hdle hh0.le
  have hscaled := mul_le_mul_of_nonneg_left hsinHalf (show 0 ≤ 4*h by positivity)
  have hsin : 2*Real.sin h ≤ 4*h*Real.sin (1/2:ℝ) := by
    linarith only [hs]
  have hrat : 4*h*Real.sin (1/2:ℝ) ≤ (23015/12000:ℝ)*h := by
    linarith only [hscaled]
  have hdmin : (985/12000:ℝ)*h ≤ d*h := by
    linarith only [hdexpr,hsin,hrat]
  nlinarith only [hdmin,hdmax,hh0]

/-- The arc angle is comparable to the square root of its small cap
deficit, with the convenient 7/4 upper coefficient. -/
theorem small_flattened_arc_sqrt_bounds
    {h d : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d = 2-2*Real.sin h/h)
    (hd0 : 0 < d) (hdle : d ≤ 1/1500) :
    Real.sqrt (3*d) ≤ h ∧ h ≤ (7/4:ℝ)*Real.sqrt d := by
  have hhhalf := small_flattened_arc_lt_half hh0 hhpi hd hdle
  have hsinLo := Real.sin_ge_sub_cube hh0.le
  have hdexpr : d*h=2*h-2*Real.sin h := by
    rw [hd]
    field_simp
  have hsmall : h^2 ≤ 1/4 := by nlinarith [sq_nonneg (h-1/2)]
  have hpow : h^5 ≤ h^3/4 := by
    have hfactor : 0 ≤ h^3*(1/4-h^2) :=
      mul_nonneg (pow_nonneg hh0.le _) (by linarith)
    nlinarith
  have hsinHi : Real.sin h ≤ h-h^3/6+h^5/100 := by
    have hb := Real.sin_bound (x := h) (by rw [abs_of_pos hh0]; linarith)
    have hu := (abs_le.mp hb).2
    rw [abs_of_pos hh0] at hu
    linarith
  have hupMul : d*h ≤ (h^2/3)*h := by
    nlinarith only [hdexpr,hsinLo]
  have hup : 3*d ≤ h^2 := by
    have hh : d ≤ h^2/3 := le_of_mul_le_mul_right hupMul hh0
    linarith
  have hlowMul : (197/600:ℝ)*h^3 ≤ d*h := by
    nlinarith only [hdexpr,hsinHi,hpow]
  have hlow : (197/600:ℝ)*h^2 ≤ d := by
    have hh : ((197/600:ℝ)*h^2)*h ≤ d*h := by
      convert hlowMul using 1 <;> ring
    exact le_of_mul_le_mul_right hh hh0
  have hsq : h^2 ≤ (49/16:ℝ)*d := by
    linarith only [hlow,sq_nonneg h]
  constructor
  · have hsqrt := Real.sq_sqrt (by linarith : 0 ≤ 3*d)
    nlinarith only [hsqrt,Real.sqrt_nonneg (3*d),hup,hh0]
  · have hsqrt := Real.sq_sqrt hd0.le
    nlinarith only [hsqrt,Real.sqrt_nonneg d,hsq,hh0]

end SpringerLean

#print axioms SpringerLean.small_flattened_arc_lt_half
#print axioms SpringerLean.small_flattened_arc_sqrt_bounds
