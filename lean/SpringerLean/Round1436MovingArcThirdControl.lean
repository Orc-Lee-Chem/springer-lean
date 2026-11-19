import SpringerLean.Round1435CosineProduct

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 100000

/-- The sixth-moment estimate pays the cubic term in the exponential
tangent correction. This is the exact numerical hinge of the moving
chord's quantitative Jensen inequality. -/
theorem movingArc_third_moment_le_three_s0_variance
    {d : ℝ} (hd0 : 0 < d) (hd : d ≤ 1/1501) :
    let b : ℝ := Real.sqrt (3*d)
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
    let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
    let third : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^3)-mean^3
    let s0 : ℝ := 2*b^2/5
    third ≤ 3*s0*var := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
  let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
  let third : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^3)-mean^3
  let s0 : ℝ := 2*b^2/5
  have hvar := movingArc_deficit_variance_lower hd0 hd
  change (995/1000:ℝ)*4*b^4/45 ≤ var at hvar
  have hthird := movingArc_deficit_third_moment_upper hd0 hd
  change third ≤ b^6*((1/7:ℝ)-(999/1000:ℝ)^3/27) at hthird
  have hnum := movingArc_third_moment_rational_margin
  have hnumMul := mul_le_mul_of_nonneg_right hnum.le
    (pow_nonneg (show 0 ≤ b by dsimp [b]; positivity) 6)
  have hvarMul := mul_le_mul_of_nonneg_left hvar (sq_nonneg b)
  change third ≤ 3*s0*var
  dsimp [s0]
  nlinarith [hnumMul,hvarMul]

end SpringerLean

#print axioms SpringerLean.movingArc_third_moment_le_three_s0_variance
