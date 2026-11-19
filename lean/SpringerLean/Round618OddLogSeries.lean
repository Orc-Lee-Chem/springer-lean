import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false

/-- The odd reciprocal-frequency kernel after removing its first mode.
The parameter x will be r⁻² in the root strip estimate. -/
theorem hasSum_odd_log_tail {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => x ^ (2*k+3) / (2*k+3 : ℝ))
      (Real.log ((1+x)/(1-x))/2-x) := by
  have hs := (Real.hasSum_log_sub_log_of_abs_lt_one (x := x)
    (by simpa only [abs_of_nonneg hx0] using hx1)).mul_left (1/2 : ℝ)
  have hall : HasSum (fun k : ℕ => x ^ (2*k+1) / (2*k+1 : ℝ))
      ((Real.log (1+x)-Real.log (1-x))/2) := by
    convert hs using 1
    · funext k
      ring
    · ring
  have ht := (hasSum_nat_add_iff' 1).mpr hall
  have ht' : HasSum (fun k : ℕ =>
      x ^ (2*(k+1)+1) / (2*(k+1)+1 : ℝ))
      ((Real.log (1+x)-Real.log (1-x))/2-x) := by
    simpa using ht
  convert ht' using 1
  · funext k
    rw [show 2*(k+1)+1 = 2*k+3 by omega]
    congr 1 <;> ring
  · rw [Real.log_div (by linarith : 1+x ≠ 0) (by linarith : 1-x ≠ 0)]

end SpringerLean
