import SpringerLean.Round1386SmoothProfileDerivs
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace SpringerLean

theorem coarseSmoothPower_second_deriv_formula
    (n : ℕ) (hn : 2 ≤ n) {x : ℝ} (hx : x < 41/20) :
    deriv (deriv (fun y : ℝ => coarseSmoothRadius y^n)) x =
      (n:ℝ)*(((n-1:ℕ):ℝ)*coarseSmoothRadius x^(n-2)*
        (deriv coarseSmoothRadius x)^2 +
        coarseSmoothRadius x^(n-1)*
          deriv (deriv coarseSmoothRadius) x) := by
  let u : ℝ → ℝ := coarseSmoothRadius
  have hU : HasDerivAt u (deriv u x) x := by
    change HasDerivAt coarseSmoothRadius (deriv coarseSmoothRadius x) x
    rw [coarseSmoothRadius_deriv hx]
    exact coarseSmoothRadius_hasDerivAt hx
  have hU₂ : HasDerivAt (deriv u)
      (deriv (deriv u) x) x := by
    change HasDerivAt (deriv coarseSmoothRadius)
      (deriv (deriv coarseSmoothRadius) x) x
    rw [coarseSmoothRadius_second_deriv hx]
    exact coarseSmoothRadius_deriv_hasDerivAt' hx
  have hpow := (hU.pow (n-1)).const_mul (n:ℝ)
  have hprod := hpow.mul hU₂
  have hsub : (n-1:ℕ)-1=n-2 := by omega
  have hprod' : HasDerivAt
      (fun y : ℝ => (n:ℝ)*u y^(n-1)*deriv u y)
      ((n:ℝ)*(((n-1:ℕ):ℝ)*u x^(n-2)*(deriv u x)^2 +
        u x^(n-1)*deriv (deriv u) x)) x := by
    convert hprod using 1
    · simp only [hsub, Pi.pow_apply]
      ring
  have hlocal : ∀ᶠ y in nhds x,
      deriv (fun z : ℝ => u z^n) y =
        (n:ℝ)*u y^(n-1)*deriv u y := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact deriv_fun_pow (coarseSmoothRadius_hasDerivAt hy).differentiableAt n
  have hDer := hprod'.congr_of_eventuallyEq
    (by filter_upwards [hlocal] with y hy; exact hy)
  change deriv (deriv (fun y : ℝ => u y^n)) x = _
  exact hDer.deriv

end SpringerLean

#print axioms SpringerLean.coarseSmoothPower_second_deriv_formula
