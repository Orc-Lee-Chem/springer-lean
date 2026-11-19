import SpringerLean.Round1516SelectedCirclePeakCaps
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The supporting tangent of a nonnegative integer power never lies
above the power. This is the scalar loss in the cap argument. -/
theorem power_tangent_le {M x : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x)
    (m : ℕ) :
    M^m+(m:ℝ)*M^(m-1)*(x-M) ≤ x^m := by
  have h := pow_add_mul_le_add_pow (a:=M) (b:=x-M)
    hM (by linarith) m
  convert h using 1 <;> ring

/-- Above the cap, the comparison power strictly exceeds its tangent.
The strictness is a consequence of strict convexity on the positive ray. -/
theorem power_tangent_lt {M x : ℝ} (hM : 0 ≤ M) (hMx : M < x)
    {m : ℕ} (hm : 2 ≤ m) :
    M^m+(m:ℝ)*M^(m-1)*(x-M) < x^m := by
  have hx : 0 ≤ x := hM.trans hMx.le
  have hs := (strictConvexOn_pow hm).lt_slope_of_hasDerivAt
    hM hx hMx (hasDerivAt_pow m M)
  rw [slope_def_field] at hs
  have hpos : 0 < x-M := sub_pos.mpr hMx
  have hmul := mul_lt_mul_of_pos_right hs hpos
  have hcancel : ((x^m-M^m)/(x-M))*(x-M)=x^m-M^m := by
    field_simp [hpos.ne']
  rw [hcancel] at hmul
  linarith

end SpringerLean

#print axioms SpringerLean.power_tangent_le
#print axioms SpringerLean.power_tangent_lt
