import SpringerLean.Round1391ArcCurvatureLower
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace SpringerLean

theorem coarseSmoothPower_contDiffAt_two
    (n : ℕ) {x : ℝ} (hx : x < 41/20) :
    ContDiffAt ℝ 2 (fun y : ℝ => coarseSmoothRadius y^n) x := by
  have hA : 0 < 41-20*x := by linarith
  unfold coarseSmoothRadius
  fun_prop (disch := positivity)

theorem coarseSmoothPower_deriv_differentiableAt
    (n : ℕ) {x : ℝ} (hx : x < 41/20) :
    DifferentiableAt ℝ (deriv (fun y : ℝ => coarseSmoothRadius y^n)) x := by
  exact ((coarseSmoothPower_contDiffAt_two n hx).derivWithin
    (m := 1) (by norm_num)).differentiableAt (by norm_num)

end SpringerLean

#print axioms SpringerLean.coarseSmoothPower_deriv_differentiableAt
