import Mathlib.Tactic

namespace SpringerLean

/-- The platform's exponential tail beats the polynomial cost from
`n=1501` onward. This is the exact scalar input to the one-sided
`39/20` radius contradiction. -/
theorem platform_exp_small (n : ℕ) (hn : 1501 ≤ n) :
    4 * (n : ℝ) ^ 2 * (39/40 : ℝ) ^ n ≤ 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
      have hq40 : (39/40 : ℝ) ^ 40 < 1/2 := by norm_num
      have hq21 : (39/40 : ℝ) ^ 21 ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      have hq : (39/40 : ℝ) ^ 1501 ≤ (1/2) ^ 37 := by
        rw [show 1501 = 40*37+21 by norm_num, pow_add, pow_mul]
        calc
          ((39/40 : ℝ)^40)^37 * (39/40 : ℝ)^21 ≤
              (1/2 : ℝ)^37 * (39/40 : ℝ)^21 := by
                exact mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (by norm_num) hq40.le 37)
                  (pow_nonneg (by norm_num) _)
          _ ≤ (1/2 : ℝ)^37 := by
            nlinarith [mul_le_mul_of_nonneg_left hq21
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) 37)]
      calc
        4 * (1501 : ℝ)^2 * (39/40 : ℝ)^1501 ≤
            4 * (1501 : ℝ)^2 * (1/2)^37 := by gcongr
        _ ≤ 1 := by norm_num
  | succ n hn ih =>
      have hnR : (1501 : ℝ) ≤ n := by exact_mod_cast hn
      have hratio : ((n : ℝ) + 1) ^ 2 * (39/40 : ℝ) ≤ (n : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℝ) - 1501)]
      have hpow : (39/40 : ℝ) ^ (n + 1) =
          (39/40 : ℝ) ^ n * (39/40) := pow_succ _ _
      rw [Nat.cast_add, Nat.cast_one, hpow]
      calc
        4 * ((n : ℝ) + 1) ^ 2 * ((39/40 : ℝ) ^ n * (39/40)) =
            4 * (((n : ℝ) + 1) ^ 2 * (39/40)) * (39/40 : ℝ) ^ n := by ring
        _ ≤ 4 * (n : ℝ) ^ 2 * (39/40 : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
          nlinarith [hratio]
        _ ≤ 1 := ih

/-- The two-cost contradiction requires only `n>16`; its numerical
margin is far larger than needed at `n≥1501`. -/
theorem one_side_cost_contradiction_scalar (n : ℕ) (hn : 1501 ≤ n) :
    (1/2 : ℝ) + 7 / n < 1 - 1 / n := by
  have hnR : (1501 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h8 : (8 : ℝ) / n < 1/2 :=
    (div_lt_iff₀ hn0).2 (by linarith)
  have hsum : (7 : ℝ)/n + 1/n = 8/n := by ring
  linarith

/-- The platform payment follows from a deliberately weak lower bound
on the comparison-circle moment.  The separate analytic input is
`2^n/(2n) ≤ I_n`; no boundary trace appears in this scalar implication. -/
theorem platform_le_of_moment_lower (n : ℕ) (hn : 1501 ≤ n)
    {I : ℝ} (hI : (2 : ℝ)^n / (2*n) ≤ I) :
    2 * (39/20 : ℝ)^n ≤ I / n := by
  have hnR : (1501 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hq := platform_exp_small n hn
  have hpow : (39/20 : ℝ)^n = (2 : ℝ)^n * (39/40 : ℝ)^n := by
    rw [show (39/20 : ℝ) = 2*(39/40) by norm_num, mul_pow]
  have hsmall : 2 * (39/40 : ℝ)^n ≤ 1 / (2*(n : ℝ)^2) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ)^2)).2
    nlinarith [hq]
  rw [hpow]
  calc
    2 * ((2 : ℝ)^n * (39/40 : ℝ)^n) =
        (2 : ℝ)^n * (2 * (39/40 : ℝ)^n) := by ring
    _ ≤ (2 : ℝ)^n * (1 / (2*(n : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hsmall (pow_nonneg (by norm_num) _)
    _ = ((2 : ℝ)^n / (2*n)) / n := by field_simp
    _ ≤ I / n := by gcongr

end SpringerLean

#print axioms SpringerLean.platform_exp_small
#print axioms SpringerLean.one_side_cost_contradiction_scalar
#print axioms SpringerLean.platform_le_of_moment_lower
