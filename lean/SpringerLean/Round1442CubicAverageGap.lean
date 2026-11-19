import SpringerLean.Round1441AffineCubicConvex

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 100000

/-- The cubic correction has an exact average gap expressed by the
variance and the raw cubic difference E[S³] − (E[S])³. -/
theorem movingArcCubicQ_average_gap
    {b : ℝ} (hb : 0 < b) (B s₀ : ℝ) :
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
    let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
    let third : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^3)-mean^3
    (1/b)*(∫ θ in (0:ℝ)..b, movingArcCubicQ B s₀ (S θ)) -
      movingArcCubicQ B s₀ mean =
      (1+B*s₀)/2*var-B/6*third := by
  dsimp
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
  let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
  let third : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^3)-mean^3
  have hInt2 : IntervalIntegrable
      (fun θ : ℝ => S θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hInt3 : IntervalIntegrable
      (fun θ : ℝ => S θ^3) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S]; fun_prop
  have hsplit : (∫ θ in (0:ℝ)..b,
      movingArcCubicQ B s₀ (S θ)) =
      ((1+B*s₀)/2)*(∫ θ in (0:ℝ)..b, S θ^2) -
        (B/6)*(∫ θ in (0:ℝ)..b, S θ^3) := by
    simp only [movingArcCubicQ]
    have hpoint (θ : ℝ) :
        (1+B*s₀)*(S θ)^2/2-B*(S θ)^3/6 =
          ((1+B*s₀)/2)*(S θ)^2-(B/6)*(S θ)^3 := by ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_sub
      (hInt2.const_mul _) (hInt3.const_mul _)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  dsimp [var,third,movingArcCubicQ]
  ring

end SpringerLean

#print axioms SpringerLean.movingArcCubicQ_average_gap
