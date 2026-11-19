import SpringerLean.Round14CircleLimit

open MeasureTheory AddCircle Filter
open scoped Topology

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- The actual forward-germ Taylor coefficient square sums converge to its
normalized circle square-modulus average at every interior radius. -/
theorem exteriorForwardGerm_circle_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
      (fun M => ∑ j ∈ Finset.range M,
        ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j))
      atTop
      (nhds (Real.circleAverage
        (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) 0 r)) := by
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hRnonneg : 0 ≤ R := by linarith
  let Rnn : NNReal := ⟨R, hRnonneg⟩
  have hRuniform := exteriorForwardGerm_uniform_on_subdisk F hc
    (r := Rnn) (by change R < 1; exact hR1)
  let point := exteriorCirclePoint r
  have hPointCont : Continuous point := by
    unfold point exteriorCirclePoint
    fun_prop
  have hPointNorm (θ : AddCircle (2 * Real.pi)) : ‖point θ‖ = r :=
    exteriorCirclePoint_norm hr0 θ
  have hMap : Set.univ ⊆ point ⁻¹' Metric.ball (0 : ℂ) R := by
    intro θ hθ
    change point θ ∈ Metric.ball (0 : ℂ) R
    rw [Metric.mem_ball, dist_zero_right, hPointNorm]
    exact hrR
  have hu := (hRuniform.comp point).mono hMap
  let p : ℕ → AddCircle (2 * Real.pi) → ℂ :=
    fun M θ => ∑ j ∈ Finset.range M,
      exteriorForwardCoeff F j * (point θ) ^ j
  let q : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => exteriorForwardGerm F (point θ)
  have hp : ∀ M, Continuous (p M) := by
    intro M
    dsimp [p]
    fun_prop
  have hq : Continuous q := by
    have hAnal := exteriorForwardGerm_analyticOnNhd_unitBall F hc
    have hmap : ∀ θ, point θ ∈ Metric.ball (0 : ℂ) 1 := by
      intro θ
      rw [Metric.mem_ball, dist_zero_right, hPointNorm]
      exact hr1
    exact hAnal.continuousOn.comp_continuous hPointCont hmap
  have hlim := circle_energy_tendsto_of_uniform p q hp hq hu
  have hfinite (M : ℕ) :
      (∫ θ : AddCircle (2 * Real.pi), ‖p M θ‖ ^ 2 ∂haarAddCircle) =
      ∑ j ∈ Finset.range M,
        ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j) := by
    change (∫ θ : AddCircle (2 * Real.pi),
      ‖∑ j ∈ Finset.range M, exteriorForwardCoeff F j *
        (exteriorCirclePoint r θ) ^ j‖ ^ 2 ∂haarAddCircle) = _
    calc
      _ = Real.circleAverage
          (fun z : ℂ => ‖∑ j ∈ Finset.range M,
            exteriorForwardCoeff F j * z ^ j‖ ^ 2) 0 r :=
        (circleAverage_eq_haar_circle _ r).symm
      _ = _ := finiteTaylor_circleAverage_energy
        (exteriorForwardCoeff F) r hr0.le M
  have hactual :
      (∫ θ : AddCircle (2 * Real.pi), ‖q θ‖ ^ 2 ∂haarAddCircle) =
      Real.circleAverage
        (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) 0 r := by
    exact (circleAverage_eq_haar_circle
      (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) r).symm
  simpa only [hfinite, hactual] using hlim

end SpringerLean