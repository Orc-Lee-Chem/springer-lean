import SpringerLean.Round1395ActualArcJensen

open MeasureTheory

namespace SpringerLean

theorem coarseArc_projection_variance_lower
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let μ : ℝ := 2*Real.sin b/b
    (99/100 : ℝ)*4*b^4/45 ≤
      (1/b)*(∫ θ in (0:ℝ)..b, (2*Real.cos θ)^2)-μ^2 := by
  dsimp
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let μ : ℝ := 2*Real.sin b/b
  let X : ℝ → ℝ := fun θ => 2*Real.cos θ
  let S : ℝ → ℝ := fun θ => 2-X θ
  have hb : 0 < b := (coarseArc_mean_bounds n hn).1
  have hbne : b ≠ 0 := ne_of_gt hb
  have hXint : IntervalIntegrable X volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [X]; fun_prop
  have hSint : IntervalIntegrable S volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S,X]; fun_prop
  have hSsqInt : IntervalIntegrable (fun θ : ℝ => S θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [S,X]; fun_prop
  have hXsqInt : IntervalIntegrable (fun θ : ℝ => X θ^2) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [X]; fun_prop
  have hXmean : (1/b)*(∫ θ in (0:ℝ)..b, X θ)=μ := by
    dsimp [X,μ]
    rw [intervalIntegral.integral_const_mul]
    simp only [integral_cos, Real.sin_zero, sub_zero]
    field_simp [hbne]
  have hSrel : (∫ θ in (0:ℝ)..b, S θ) =
      2*b-(∫ θ in (0:ℝ)..b, X θ) := by
    dsimp [S]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hXint]
    simp
    ring
  have hSmean : (1/b)*(∫ θ in (0:ℝ)..b, S θ)=2-μ := by
    rw [hSrel]
    have hbdiv : (1/b)*b=1 := by field_simp [hbne]
    nlinarith [hXmean]
  have hXsqrel : (∫ θ in (0:ℝ)..b, X θ^2) =
      (∫ θ in (0:ℝ)..b, S θ^2) +
      4*(∫ θ in (0:ℝ)..b, X θ)-4*b := by
    have hpoint (θ : ℝ) : X θ^2=S θ^2+4*X θ-4 := by
      dsimp [X,S]
      ring
    simp_rw [hpoint]
    have hSX : IntervalIntegrable (fun θ : ℝ => S θ^2+4*X θ) volume 0 b := by
      exact hSsqInt.add (hXint.const_mul _)
    rw [intervalIntegral.integral_sub hSX intervalIntegrable_const]
    rw [intervalIntegral.integral_add hSsqInt (hXint.const_mul _)]
    rw [intervalIntegral.integral_const_mul]
    simp
    ring
  have hSVar := coarseArc_deficit_variance_lower n hn
  dsimp [S,X,b] at hSVar
  change (1/b)*(∫ θ in (0:ℝ)..b, S θ^2) -
    ((1/b)*(∫ θ in (0:ℝ)..b, S θ))^2 ≥
    (99/100 : ℝ)*4*b^4/45 at hSVar
  have hXnorm : (1/b)*(∫ θ in (0:ℝ)..b, X θ^2) =
      (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)+4*μ-4 := by
    rw [hXsqrel]
    have hbdiv : (1/b)*b=1 := by field_simp [hbne]
    nlinarith [hXmean]
  change (99/100 : ℝ)*4*b^4/45 ≤
    (1/b)*(∫ θ in (0:ℝ)..b, X θ^2)-μ^2
  rw [hXnorm]
  nlinarith [hSmean,hSVar]

end SpringerLean

#print axioms SpringerLean.coarseArc_projection_variance_lower
