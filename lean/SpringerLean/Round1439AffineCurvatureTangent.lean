import SpringerLean.Round1438AffineMovingCurvature

namespace SpringerLean
set_option maxHeartbeats 100000

/-- The exponential curvature is bounded below by its tangent at an
arbitrary reference deficit `s₀`. -/
theorem refinedAffineSmoothPower_curvature_tangent
    (n : ℕ) (hn : 1501 ≤ n)
    {W s s₀ : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hs0 : 0 ≤ s) (hns : (n:ℝ)*s ≤ 3) :
    let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)
    let B : ℝ := (n:ℝ)/2
    A*Real.exp (-B*s₀)*(1+B*(s₀-s)) ≤
      deriv (deriv (refinedAffineSmoothPower W n)) s := by
  dsimp
  let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
    (2:ℝ)^(n-2)
  let B : ℝ := (n:ℝ)/2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hExp := Real.add_one_le_exp (B*(s₀-s))
  have hMul := mul_le_mul_of_nonneg_left hExp
    (mul_nonneg hA (Real.exp_pos (-B*s₀)).le)
  have hExpEq : Real.exp (-B*s) =
      Real.exp (-B*s₀)*Real.exp (B*(s₀-s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbase := refinedAffineSmoothPower_curvature_lower n hn
    hW0 hW hs0 hns
  have hbase' : A*Real.exp (-B*s) ≤
      deriv (deriv (refinedAffineSmoothPower W n)) s := by
    change A*Real.exp (-((n:ℝ)/2)*s) ≤ _
    rw [show -((n:ℝ)/2)*s = -(n:ℝ)*s/2 by ring]
    exact hbase
  rw [hExpEq] at hbase'
  change A*Real.exp (-B*s₀)*(1+B*(s₀-s)) ≤ _
  calc
    A*Real.exp (-B*s₀)*(1+B*(s₀-s)) ≤
        A*Real.exp (-B*s₀)*Real.exp (B*(s₀-s)) := by
      simpa only [add_comm] using hMul
    _ = A*(Real.exp (-B*s₀)*Real.exp (B*(s₀-s))) := by ring
    _ ≤ _ := hbase'

end SpringerLean

#print axioms SpringerLean.refinedAffineSmoothPower_curvature_tangent
