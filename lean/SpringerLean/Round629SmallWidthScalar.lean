import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SpringerLean
set_option Elab.async false

/-- A sufficient exact lower enclosure for the logarithm in Appendix B.2.
It uses the fixed library's proved numerical log enclosures. -/
theorem smallWidth_log_ten_thousand_gt :
    (921 : ℝ)/100 < Real.log 10000 := by
  rw [show (10000 : ℝ) = (10 : ℝ)^4 by norm_num,
    Real.log_pow,Real.log_ten_eq]
  nlinarith [Real.log_two_gt_d9,Real.log_five_gt_d9]

/-- Uniform last scalar step of the small-deficit width estimate. The
actual map's two preceding width estimates remain separate obligations. -/
theorem smallWidth_ratio_sq_lt
    {L : ℝ} (hL : Real.log 10000 ≤ L) :
    ((166973 : ℝ)/1000000/Real.sqrt L +
      Real.sqrt (1/4+(92120 : ℝ)/1000000/L))^2 <
        (31914 : ℝ)/100000 := by
  have hlow : (921 : ℝ)/100 ≤ L := smallWidth_log_ten_thousand_gt.le.trans hL
  have hL0 : 0 < L := by linarith
  have hlo2 : ((3034798 : ℝ)/1000000)^2 ≤ (921 : ℝ)/100 := by norm_num
  have hsL := Real.sq_sqrt hL0.le
  have hlo : (3034798 : ℝ)/1000000 ≤ Real.sqrt L := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg L)).mp
    rw [hsL]
    exact hlo2.trans hlow
  have hfirst : (166973 : ℝ)/1000000/Real.sqrt L ≤
      ((166973 : ℝ)/1000000)/((3034798 : ℝ)/1000000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
  have hfrac : (92120 : ℝ)/1000000/L ≤
      ((92120 : ℝ)/1000000)/((921 : ℝ)/100) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlow
  have hhi2 : (1 : ℝ)/4+((92120 : ℝ)/1000000)/((921 : ℝ)/100) ≤
      ((509905 : ℝ)/1000000)^2 := by norm_num
  have harg : 0 ≤ (1 : ℝ)/4+(92120 : ℝ)/1000000/L := by positivity
  have hsecond : Real.sqrt (1/4+(92120 : ℝ)/1000000/L) ≤
      (509905 : ℝ)/1000000 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
    rw [Real.sq_sqrt harg]
    linarith
  have hsum := add_le_add hfirst hsecond
  have hsq :
      ((166973 : ℝ)/1000000/Real.sqrt L +
        Real.sqrt (1/4+(92120 : ℝ)/1000000/L))^2 ≤
      (((166973 : ℝ)/1000000)/((3034798 : ℝ)/1000000)+
        (509905 : ℝ)/1000000)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  exact hsq.trans_lt (by norm_num)

theorem smallWidth_first_term_ratio_lt
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ (707107 : ℝ)/50000000) :
    ((4 : ℝ)/25+((2/25 : ℝ)^2+1/2)*s)/(1+(2/25 : ℝ)*s) <
      (166973 : ℝ)/1000000 := by
  have hden : 0 < 1+(2/25 : ℝ)*s := by positivity
  apply (div_lt_iff₀ hden).mpr
  nlinarith

end SpringerLean
