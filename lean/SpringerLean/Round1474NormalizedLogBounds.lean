import SpringerLean.Round1473PositiveTermInterval
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace SpringerLean
set_option maxHeartbeats 200000

/-- The logarithmic width divided by the order decreases from the
base order, uniformly for deficits at least `3/20`. -/
theorem refinedAffine_log_over_order_bound
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : (3/20:ℝ) ≤ t) :
    Real.log (2*(n:ℝ)/t)/(n:ℝ) ≤
      Real.log (2*(1501:ℝ)/(3/20:ℝ))/1501 := by
  let N : ℝ := n
  let x : ℝ := 2*N/(3/20:ℝ)
  let x₀ : ℝ := 2*(1501:ℝ)/(3/20:ℝ)
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have ht : 0 < t := by linarith
  have hx0 : Real.exp 1 ≤ x₀ := by
    have h := Real.exp_one_lt_three
    dsimp [x₀]
    norm_num at *
    linarith
  have hx : x₀ ≤ x := by dsimp [x₀,x]; nlinarith
  have hmono := Real.log_div_self_antitoneOn hx0 (hx0.trans hx) hx
  have hlog : Real.log (2*N/t) ≤ Real.log x := by
    apply Real.log_le_log (by positivity)
    dsimp [x]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) ht0
  have hscaled : Real.log (2*N/t)/N ≤ Real.log x/N :=
    div_le_div_of_nonneg_right hlog hN0.le
  have horder : Real.log x/N ≤ Real.log x₀/1501 := by
    have heq : x/N=2/(3/20:ℝ) := by dsimp [x]; field_simp
    have heq0 : x₀/(1501:ℝ)=2/(3/20:ℝ) := by dsimp [x₀]; norm_num
    have hxpos : 0 < x := by dsimp [x]; positivity
    have hx0pos : 0 < x₀ := by dsimp [x₀]; positivity
    have hscale := mul_le_mul_of_nonneg_left hmono
      (by norm_num : (0:ℝ) ≤ 2/(3/20:ℝ))
    have hleft : 2/(3/20:ℝ)*(Real.log x/x)=Real.log x/N := by
      rw [←heq]
      field_simp
    have hright : 2/(3/20:ℝ)*(Real.log x₀/x₀)=
        Real.log x₀/1501 := by
      rw [←heq0]
      field_simp
    rw [hleft,hright] at hscale
    exact hscale
  exact hscaled.trans horder

/-- The squared logarithmic width has the same order normalization.
This is a direct application of the mathlib monotonicity of
`log x / sqrt x` beyond `exp 2`. -/
theorem refinedAffine_log_sq_over_order_bound
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : (3/20:ℝ) ≤ t) (ht1 : t ≤ 1) :
    (Real.log (2*(n:ℝ)/t))^2/(n:ℝ) ≤
      (Real.log (2*(1501:ℝ)/(3/20:ℝ)))^2/1501 := by
  let N : ℝ := n
  let x : ℝ := 2*N/(3/20:ℝ)
  let x₀ : ℝ := 2*(1501:ℝ)/(3/20:ℝ)
  have hN : (1501:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have ht : 0 < t := by linarith
  have hx0 : Real.exp 2 ≤ x₀ := by
    have h := Real.exp_one_lt_three
    have heq : Real.exp 2=(Real.exp 1)^2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [heq]
    dsimp [x₀]
    nlinarith [Real.exp_pos 1]
  have hx : x₀ ≤ x := by dsimp [x₀,x]; nlinarith
  have hmono := Real.log_div_sqrt_antitoneOn hx0 (hx0.trans hx) hx
  have hlog0 : 0 ≤ Real.log (2*N/t) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ ht).2
    nlinarith
  have hlog : Real.log (2*N/t) ≤ Real.log x := by
    apply Real.log_le_log (by positivity)
    dsimp [x]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) ht0
  have hlogx : 0 ≤ Real.log x := by
    have h1 : 1 ≤ x := by
      have hh : (1:ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp 2]
      linarith
    exact Real.log_nonneg h1
  have hlogx0 : 0 ≤ Real.log x₀ := by
    have h1 : (1:ℝ) ≤ Real.exp 2 := by nlinarith [Real.add_one_le_exp 2]
    exact Real.log_nonneg (h1.trans hx0)
  have hsq0 := pow_le_pow_left₀ hlog0 hlog 2
  have hsq : (Real.log (2*N/t))^2/N ≤ (Real.log x)^2/N :=
    div_le_div_of_nonneg_right hsq0 hN0.le
  have hrootx : (Real.sqrt x)^2=x := Real.sq_sqrt (by dsimp [x]; positivity)
  have hrootx0 : (Real.sqrt x₀)^2=x₀ := Real.sq_sqrt (by dsimp [x₀]; positivity)
  have hmonosq := pow_le_pow_left₀
    (div_nonneg hlogx (Real.sqrt_nonneg x)) hmono 2
  have heq : x/N=2/(3/20:ℝ) := by dsimp [x]; field_simp
  have heq0 : x₀/(1501:ℝ)=2/(3/20:ℝ) := by dsimp [x₀]; norm_num
  have horder : (Real.log x)^2/N ≤ (Real.log x₀)^2/1501 := by
    have hscale := mul_le_mul_of_nonneg_left hmonosq
      (by norm_num : (0:ℝ) ≤ 2/(3/20:ℝ))
    have hleft : 2/(3/20:ℝ)*(Real.log x/Real.sqrt x)^2 =
        (Real.log x)^2/N := by
      rw [div_pow, hrootx, ← heq]
      field_simp [show x ≠ 0 by dsimp [x]; positivity]
    have hright : 2/(3/20:ℝ)*(Real.log x₀/Real.sqrt x₀)^2 =
        (Real.log x₀)^2/1501 := by
      rw [div_pow, hrootx0, ← heq0]
      field_simp [show x₀ ≠ 0 by dsimp [x₀]; positivity]
    rw [hleft,hright] at hscale
    exact hscale
  exact hsq.trans horder

end SpringerLean

#print axioms SpringerLean.refinedAffine_log_over_order_bound
#print axioms SpringerLean.refinedAffine_log_sq_over_order_bound
