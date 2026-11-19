import SpringerLean.Round1522FlatModelLevelNonneg

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The centered Poisson peak of the mean-preserving flattened cosine
profile is nonnegative at every positive inner radius. -/
theorem flattenedCosinePoissonAtReal_nonneg
    (h : ℝ) (hh0 : 0 < h) (hhpi : h < Real.pi)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ flattenedCosinePoissonAtReal h r := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2*Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2*Real.pi)
  let u : ℝ → ℝ := cappedAngularCosine (2*Real.sin h/h) h
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let B : ℝ := |2*Real.sin h/h|+2
  let M : ℝ := (1-r^2)/(1-r)^2
  have huMeas : Measurable u := by
    dsimp [u,cappedAngularCosine]
    exact Measurable.ite (measurableSet_Ioc.union measurableSet_Icc)
      measurable_const (by fun_prop)
  have huBound (θ : ℝ) : |u θ| ≤ B := by
    classical
    by_cases hθ : θ ∈ centeredAngularArc h
    · simp only [u,cappedAngularCosine,if_pos hθ]
      dsimp [B]
      linarith
    · simp only [u,cappedAngularCosine,if_neg hθ]
      dsimp [B]
      calc
        |2*Real.cos θ| = 2*|Real.cos θ| := by simp
        _ ≤ 2 := by nlinarith [Real.abs_cos_le_one θ]
        _ ≤ |2*Real.sin h/h|+2 := by linarith [abs_nonneg (2*Real.sin h/h)]
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hP0 (θ : ℝ) : 0 ≤ P θ :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).1
  have hPM (θ : ℝ) : P θ ≤ M :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).2
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hlevels (t : ℝ) (ht : 0 < t) (_htM : t ≤ M) :
      (∫ θ in {θ | t ≤ P θ}, -u θ ∂μ) ≤ 0 := by
    have h := cappedAngularCosine_poisson_level_nonneg
      h hh0 hhpi hr0 hr1 ht
    change 0 ≤ ∫ θ in {θ | t ≤ P θ}, u θ ∂μ at h
    rw [integral_neg]
    linarith
  have hweighted := bounded_weighted_integral_nonpos_of_levels
    μ (fun θ => -u θ) P huMeas.neg hPc.measurable
      B M hB0 (by intro θ; simpa using huBound θ) hP0 hPM hlevels
  have hrewrite : (∫ θ, (-u θ)*P θ ∂μ) =
      -(∫ θ,u θ*P θ ∂μ) := by
    simp_rw [neg_mul]
    rw [integral_neg]
  rw [hrewrite] at hweighted
  have hraw : 0 ≤ ∫ θ,u θ*P θ ∂μ := by linarith
  change 0 ≤ (2*Real.pi)⁻¹ * (∫ θ,u θ*P θ ∂μ)
  exact mul_nonneg (by positivity) hraw

end SpringerLean

#print axioms SpringerLean.flattenedCosinePoissonAtReal_nonneg
