import SpringerLean.Round1437MovingPowerExponential
import Mathlib.Analysis.Calculus.Deriv.Pow

open Filter

namespace SpringerLean
set_option maxHeartbeats 200000

noncomputable def refinedAffineSmoothPower
    (W : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  (2*refinedAffineU W-refinedAffineV W*s)^n

theorem refinedAffineSmoothPower_second_deriv
    (W : ℝ) (n : ℕ) (hn : 2 ≤ n) (s : ℝ) :
    deriv (deriv (refinedAffineSmoothPower W n)) s =
      (n:ℝ)*((n-1:ℕ):ℝ)*(refinedAffineV W)^2*
        (2*refinedAffineU W-refinedAffineV W*s)^(n-2) := by
  let a : ℝ → ℝ := fun y => 2*refinedAffineU W-refinedAffineV W*y
  have ha (y : ℝ) : HasDerivAt a (-refinedAffineV W) y := by
    have hh := ((hasDerivAt_id y).const_mul (-refinedAffineV W)).const_add
      (2*refinedAffineU W)
    convert hh using 1
    · funext x; dsimp [a]; ring
    · ring
  have hpow := ((ha s).pow (n-1)).const_mul
    ((n:ℝ)*(-refinedAffineV W))
  have hsub : n-1-1=n-2 := by omega
  have hpow' : HasDerivAt
      (fun y : ℝ => (n:ℝ)*(-refinedAffineV W)*a y^(n-1))
      ((n:ℝ)*((n-1:ℕ):ℝ)*(refinedAffineV W)^2*
        a s^(n-2)) s := by
    convert hpow using 1
    · simp only [hsub]
      ring
  have hlocal : ∀ᶠ y in nhds s,
      deriv (refinedAffineSmoothPower W n) y =
        (n:ℝ)*(-refinedAffineV W)*a y^(n-1) := by
    filter_upwards [] with y
    change deriv (fun z : ℝ => a z^n) y = _
    have hh := deriv_fun_pow (ha y).differentiableAt n
    rw [(ha y).deriv] at hh
    convert hh using 1 <;> ring
  have hDer := hpow'.congr_of_eventuallyEq
    (by filter_upwards [hlocal] with y hy; exact hy)
  change deriv (deriv (refinedAffineSmoothPower W n)) s = _
  exact hDer.deriv

/-- The active affine power keeps a pointwise exponential curvature
lower bound; the exponent depends on the current deficit `s`. -/
theorem refinedAffineSmoothPower_curvature_lower
    (n : ℕ) (hn : 1501 ≤ n)
    {W s : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hs0 : 0 ≤ s) (hns : (n:ℝ)*s ≤ 3) :
    (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)*Real.exp (-(n:ℝ)*s/2) ≤
        deriv (deriv (refinedAffineSmoothPower W n)) s := by
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hs : s ≤ 3/(n:ℝ) := (le_div_iff₀ hn0).2 (by nlinarith [hns])
  have hsOne : s/2 < 1 := by
    have hnlarge : (1501:ℝ)≤n := by exact_mod_cast hn
    have hdiv : (3:ℝ)/(n:ℝ) < 1 :=
      (div_lt_iff₀ hn0).2 (by linarith)
    linarith
  have hbase0 : 0 ≤ 2-s := by linarith
  have hbase : 2-s ≤
      2*refinedAffineU W-refinedAffineV W*s := by
    dsimp [refinedAffineU,refinedAffineV]
    nlinarith [sq_nonneg W,mul_nonneg hW0 hs0]
  have hpow : (2-s)^(n-2) ≤
      (2*refinedAffineU W-refinedAffineV W*s)^(n-2) :=
    pow_le_pow_left₀ hbase0 hbase _
  have hexp := movingArc_power_exponential_lower n hn3 hs0
    (hns.trans (by norm_num))
  have hscale : (2:ℝ)^(n-2)*Real.exp (-(n:ℝ)*s/2) ≤
      (2-s)^(n-2) := by
    have hh := mul_le_mul_of_nonneg_left hexp
      (pow_nonneg (by norm_num : (0:ℝ)≤2) (n-2))
    have heq : (2-s)^(n-2)=(2:ℝ)^(n-2)*(1-s/2)^(n-2) := by
      rw [show 2-s=2*(1-s/2) by ring,mul_pow]
    rw [heq]
    exact hh
  have hcoef : 0 ≤ (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ) := by
    positivity
  have htotal := mul_le_mul_of_nonneg_left (hscale.trans hpow) hcoef
  rw [refinedAffineSmoothPower_second_deriv W n hn2]
  nlinarith [htotal]

end SpringerLean

#print axioms SpringerLean.refinedAffineSmoothPower_second_deriv
#print axioms SpringerLean.refinedAffineSmoothPower_curvature_lower
