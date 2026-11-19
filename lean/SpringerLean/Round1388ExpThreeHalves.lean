import SpringerLean.Round1387PowerCurvatureFormula
import Mathlib.Analysis.Complex.Exponential

namespace SpringerLean

/-- A short rational exponential bound used only to make the arc
curvature constant `1/5` transparent. -/
theorem exp_three_halves_lt_nine_halves :
    Real.exp (3/2 : ℝ) < 9/2 := by
  have h1 : Real.exp (1:ℝ) ≤ 109/40 := by
    have h := Real.exp_bound' (x := (1:ℝ)) (n := 8)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hhalf : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have h := Real.exp_bound' (x := (1/2:ℝ)) (n := 8)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hsplit : (3/2 : ℝ)=1+1/2 := by norm_num
  rw [hsplit, Real.exp_add]
  calc
    Real.exp (1:ℝ)*Real.exp (1/2 : ℝ) ≤
        (109/40 : ℝ)*Real.exp (1/2 : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ (109/40 : ℝ)*(33/20 : ℝ) :=
      mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ < 9/2 := by norm_num

end SpringerLean

#print axioms SpringerLean.exp_three_halves_lt_nine_halves
