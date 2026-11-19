import SpringerLean.Round27UniformTail

open MeasureTheory Set Filter Metric
open scoped Topology

namespace SpringerLean

/-- On any fixed circle, the angular average of the actual compensated
vertical tail tends to zero. The logarithms remain paired as one integrable
difference throughout. -/
theorem regularExterior_vertical_difference_tail_circleAverage_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (c : ℂ) (ρ : ℝ) :
    Tendsto (fun n : ℕ =>
      Real.circleAverage
        (fun z : ℂ => ∫ y in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
          regularExteriorVerticalPotentialDifference F s ξ z.re y) c ρ)
      atTop (𝓝 0) := by
  let D : ℕ → ℝ → ℝ := fun n a =>
    ∫ y in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
      regularExteriorVerticalPotentialDifference F s ξ a y
  let A : ℕ → ℝ → ℝ := fun n a =>
    ∫ y in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
      |regularExteriorVerticalPotentialDifference F s ξ a y|
  let K : Set ℝ := Complex.re '' sphere c |ρ|
  have hK : IsCompact K := (isCompact_sphere c |ρ|).image Complex.continuous_re
  have hU := regularExterior_vertical_difference_abs_tail_uniformOn
    F hc hs0 hs1 ξ K hK
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hDcont (n : ℕ) : Continuous (D n) := by
    let C : NNReal := ⟨2 * Real.pi, hpi⟩
    have hlip : LipschitzWith C (D n) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simp only [Real.dist_eq]
      exact regularExterior_vertical_difference_setIntegral_lipschitz_horizontal
        F hc hs0 hs1 ξ _ a b
    exact hlip.continuous
  have hDci (n : ℕ) : CircleIntegrable (fun z : ℂ => D n z.re) c ρ :=
    ((hDcont n).comp Complex.continuous_re).continuousOn.circleIntegrable'
  have hDabsci (n : ℕ) : CircleIntegrable (fun z : ℂ => |D n z.re|) c ρ :=
    (((hDcont n).comp Complex.continuous_re).abs).continuousOn.circleIntegrable'
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (ε / 2) hhalf]
    with n hn
  have hpoint (z : ℂ) (hz : z ∈ sphere c |ρ|) :
      |D n z.re| ≤ ε / 2 := by
    have hA : A n z.re < ε / 2 := by
      have hmem : z.re ∈ K := ⟨z, hz, rfl⟩
      have h := hn z.re hmem
      have hnonneg : 0 ≤ A n z.re := by
        dsimp [A]
        exact integral_nonneg (fun _ => abs_nonneg _)
      simpa [Real.dist_eq, abs_sub_comm, abs_of_nonneg hnonneg, A] using h
    have hD : |D n z.re| ≤ A n z.re := by
      exact abs_integral_le_integral_abs
    exact le_trans hD hA.le
  have hcircle : Real.circleAverage (fun z : ℂ => |D n z.re|) c ρ ≤ ε / 2 :=
    Real.circleAverage_mono_on_of_le_circle (hDabsci n) hpoint
  have hbound : |Real.circleAverage (fun z : ℂ => D n z.re) c ρ| ≤ ε / 2 :=
    le_trans Real.abs_circleAverage_le_circleAverage_abs hcircle
  change dist (Real.circleAverage (fun z : ℂ => D n z.re) c ρ) 0 < ε
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hbound (by linarith)

end SpringerLean