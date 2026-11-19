import SpringerLean.Round1342ActualAffineCap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace SpringerLean

/-- A positive-part power lies below the exponential envelope. This is
the elementary pointwise input for a Gaussian bound on the coarse
one-end circle cost. -/
theorem positivePart_one_sub_pow_le_exp
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (max 0 (1-t))^n ≤ Real.exp (-(n:ℝ)*t) := by
  by_cases hbase : 1-t ≤ 0
  · have hmax : max (0:ℝ) (1-t) = 0 := max_eq_left hbase
    rw [hmax, zero_pow (by omega : n ≠ 0)]
    exact (Real.exp_pos _).le
  · have hbase0 : 0 ≤ 1-t := le_of_lt (lt_of_not_ge hbase)
    have hle : 1-t ≤ Real.exp (-t) := by
      nlinarith [Real.add_one_le_exp (-t)]
    have hpow := pow_le_pow_left₀ hbase0 hle n
    rw [max_eq_right hbase0]
    calc
      (1-t)^n ≤ (Real.exp (-t))^n := hpow
      _ = Real.exp (-(n:ℝ)*t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- The normalized affine cap has a Gaussian quadratic loss throughout
the principal angular interval. -/
theorem affineCos_le_gaussianBase {θ : ℝ}
    (hθ : |θ| ≤ Real.pi) :
    (1/5 : ℝ)+(4/5)*Real.cos θ ≤
      1-(8/5 : ℝ)/Real.pi^2*θ^2 := by
  have hc := Real.cos_le_one_sub_mul_cos_sq hθ
  have hh := mul_le_mul_of_nonneg_left hc
    (by norm_num : (0:ℝ) ≤ 4/5)
  calc
    (1/5 : ℝ)+(4/5)*Real.cos θ ≤
        (1/5)+(4/5)*(1-2/Real.pi^2*θ^2) := by
      simpa only [add_comm] using add_le_add_left hh (1/5 : ℝ)
    _ = 1-(8/5 : ℝ)/Real.pi^2*θ^2 := by ring

/-- A platform maximum pays at most one platform term plus the positive
part of the other term. -/
theorem max_pow_le_platform_add_pospart
    (n : ℕ) {c b : ℝ} (hc : 0 ≤ c) :
    (max c b)^n ≤ c^n + (max 0 b)^n := by
  rcases le_total b c with h | h
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (pow_nonneg (le_max_left _ _) _)
  · rw [max_eq_right h, max_eq_right (hc.trans h)]
    exact le_add_of_nonneg_left (pow_nonneg hc _)

/-- A fully pointwise Gaussian envelope for the coarse convex profile.
The remaining step for the one-end contradiction is its normalized
circle integral and the comparison with the Catalan candidate. -/
theorem affinePlatformPower_le_gaussian
    (n : ℕ) (hn : 1 ≤ n) {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n ≤
      (39/20 : ℝ)^n + (2:ℝ)^n *
        Real.exp (-(n:ℝ)*((8/5 : ℝ)/Real.pi^2*θ^2)) := by
  let b : ℝ := (1/5)+(4/5)*Real.cos θ
  let t : ℝ := (8/5 : ℝ)/Real.pi^2*θ^2
  have hb : b ≤ 1-t := affineCos_le_gaussianBase hθ
  have hmax : max (0:ℝ) b ≤ max 0 (1-t) := max_le_max_left 0 hb
  have hpow : (max (0:ℝ) b)^n ≤ Real.exp (-(n:ℝ)*t) :=
    (pow_le_pow_left₀ (le_max_left _ _) hmax n).trans
      (positivePart_one_sub_pow_le_exp n hn t)
  have hscale : (2/5 : ℝ)+(8/5)*Real.cos θ = 2*b := by dsimp [b]; ring
  have hposscale : max (0:ℝ) (2*b) = 2*max 0 b := by
    rcases le_total b 0 with h | h
    · have h2 : 2*b ≤ 0 := by nlinarith
      rw [max_eq_left h, max_eq_left h2]
      ring
    · have h2 : 0 ≤ 2*b := by positivity
      rw [max_eq_right h, max_eq_right h2]
  rw [hscale]
  have hplatform := max_pow_le_platform_add_pospart n
    (c := (39/20 : ℝ)) (b := 2*b) (by norm_num)
  rw [hposscale, mul_pow] at hplatform
  calc
    (max (39/20 : ℝ) (2*b))^n ≤
        (39/20 : ℝ)^n + (2:ℝ)^n*(max 0 b)^n := hplatform
    _ ≤ (39/20 : ℝ)^n + (2:ℝ)^n*Real.exp (-(n:ℝ)*t) := by
      gcongr

end SpringerLean

#print axioms SpringerLean.positivePart_one_sub_pow_le_exp
#print axioms SpringerLean.affineCos_le_gaussianBase
#print axioms SpringerLean.max_pow_le_platform_add_pospart
#print axioms SpringerLean.affinePlatformPower_le_gaussian
