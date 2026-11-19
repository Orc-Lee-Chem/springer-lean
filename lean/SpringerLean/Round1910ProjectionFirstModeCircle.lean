import SpringerLean.Round1909PowerTestLocalConvex
import SpringerLean.Round14ActualParseval

open MeasureTheory AddCircle Filter Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

noncomputable def projectionAnalyticCoeff
    (F : ℂ → ℂ) (c : ℂ) (j : ℕ) : ℂ :=
  c * exteriorForwardCoeff F j + if j = 1 then conj c else 0

private theorem projectionAnalytic_partial_eq
    (F : ℂ → ℂ) (c z : ℂ) (M : ℕ) (hM : 2 ≤ M) :
    (∑ j ∈ Finset.range M, projectionAnalyticCoeff F c j * z ^ j) =
      conj c * z + c *
        ∑ j ∈ Finset.range M, exteriorForwardCoeff F j * z ^ j := by
  simp only [projectionAnalyticCoeff, add_mul, Finset.sum_add_distrib]
  have h1 : 1 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
  simp [h1]
  rw [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The first Taylor mode of the analytic reflection of the real
projection survives in its full circle square energy. -/
theorem projectionAnalytic_circle_energy_first_mode
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 * r ^ 2 ≤
      Real.circleAverage
        (fun z : ℂ => ‖projectionAnalytic F c z‖ ^ 2) 0 r := by
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  let Rnn : NNReal := ⟨R, by linarith⟩
  have hRuniform := exteriorForwardGerm_uniform_on_subdisk F hc
    (r := Rnn) (by change R < 1; exact hR1)
  let point := exteriorCirclePoint r
  have hPointCont : Continuous point := by
    unfold point exteriorCirclePoint
    fun_prop
  have hPointNorm (θ : AddCircle (2 * Real.pi)) : ‖point θ‖ = r :=
    exteriorCirclePoint_norm hr0 θ
  have hMap : Set.univ ⊆ point ⁻¹' ball (0 : ℂ) R := by
    intro θ hθ
    change point θ ∈ ball (0 : ℂ) R
    rw [mem_ball, dist_zero_right, hPointNorm]
    exact hrR
  have hu0 := (hRuniform.comp point).mono hMap
  let p : ℕ → AddCircle (2 * Real.pi) → ℂ :=
    fun M θ => conj c * point θ + c *
      ∑ j ∈ Finset.range (M + 2),
        exteriorForwardCoeff F j * (point θ) ^ j
  let q : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => projectionAnalytic F c (point θ)
  have hp : ∀ M, Continuous (p M) := by
    intro M
    dsimp [p]
    fun_prop
  have hq : Continuous q := by
    have hMap1 : ∀ θ, point θ ∈ ball (0 : ℂ) 1 := by
      intro θ
      rw [mem_ball, dist_zero_right, hPointNorm]
      exact hr1
    exact (projectionAnalytic_analyticOnNhd F hc c).continuousOn.comp_continuous
      hPointCont hMap1
  have hu : TendstoUniformlyOn p q atTop Set.univ := by
    have hu2 : TendstoUniformlyOn
        (fun M θ => ∑ j ∈ Finset.range (M + 2),
          exteriorForwardCoeff F j * (point θ) ^ j)
        (fun θ => exteriorForwardGerm F (point θ)) atTop Set.univ := by
      intro U hU
      have h := (tendsto_add_atTop_nat 2).eventually (hu0 U hU)
      simpa only [Function.comp_def] using h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu2) (ε / max 1 ‖c‖)
      (div_pos hε (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (le_max_left _ _)))] with M hM θ hθ
    have hh := hM θ hθ
    dsimp [p,q,projectionAnalytic]
    rw [dist_eq_norm]
    have heq :
        (conj c * point θ + c *
          ∑ j ∈ Finset.range (M + 2),
            exteriorForwardCoeff F j * point θ ^ j) -
          (conj c * point θ + c * exteriorForwardGerm F (point θ)) =
        c * ((∑ j ∈ Finset.range (M + 2),
            exteriorForwardCoeff F j * point θ ^ j) -
          exteriorForwardGerm F (point θ)) := by ring
    rw [norm_sub_rev, heq, norm_mul]
    have hcmax : ‖c‖ ≤ max 1 ‖c‖ := le_max_right _ _
    have hmaxpos : 0 < max 1 ‖c‖ :=
      lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hbound : ‖c‖ * (ε / max 1 ‖c‖) ≤ ε := by
      calc
        _ ≤ max 1 ‖c‖ * (ε / max 1 ‖c‖) :=
          mul_le_mul_of_nonneg_right hcmax (div_nonneg hε.le hmaxpos.le)
        _ = ε := by field_simp
    rw [dist_eq_norm, norm_sub_rev] at hh
    by_cases hc0 : ‖c‖ = 0
    · simp [hc0, hε]
    · have hcpos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc0)
      exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hh hcpos) hbound
  have hlim := circle_energy_tendsto_of_uniform p q hp hq hu
  have hfinite (M : ℕ) :
      ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 * r ^ 2 ≤
        ∫ θ : AddCircle (2 * Real.pi), ‖p M θ‖ ^ 2 ∂haarAddCircle := by
    have hpoly (z : ℂ) :
        (∑ j ∈ Finset.range (M + 2),
          projectionAnalyticCoeff F c j * z ^ j) =
          conj c * z + c *
            ∑ j ∈ Finset.range (M + 2),
              exteriorForwardCoeff F j * z ^ j :=
      projectionAnalytic_partial_eq F c z (M + 2) (by omega)
    have henergy := finiteTaylor_circleAverage_energy
      (projectionAnalyticCoeff F c) r hr0.le (M + 2)
    rw [circleAverage_eq_haar_circle] at henergy
    have heq : (∫ θ : AddCircle (2 * Real.pi),
        ‖p M θ‖ ^ 2 ∂haarAddCircle) =
        ∑ j ∈ Finset.range (M + 2),
          ‖projectionAnalyticCoeff F c j‖ ^ 2 * r ^ (2 * j) := by
      convert henergy using 1
      congr 1
      funext θ
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpoly (point θ)).symm
    rw [heq]
    have h1 : 1 ∈ Finset.range (M + 2) := Finset.mem_range.mpr (by omega)
    have hsum :
        ‖projectionAnalyticCoeff F c 1‖ ^ 2 * r ^ (2 * 1) ≤
          ∑ j ∈ Finset.range (M + 2),
            ‖projectionAnalyticCoeff F c j‖ ^ 2 * r ^ (2 * j) :=
      Finset.single_le_sum
        (f := fun j : ℕ => ‖projectionAnalyticCoeff F c j‖ ^ 2 * r ^ (2 * j))
        (fun j hj => by positivity) h1
    have hcoef : projectionAnalyticCoeff F c 1 =
        conj c + c * exteriorForwardCoeff F 1 := by
      simp [projectionAnalyticCoeff, add_comm]
    rw [hcoef] at hsum
    simpa only [Nat.reduceMul] using hsum
  have hresult := ge_of_tendsto hlim (Filter.Eventually.of_forall hfinite)
  rw [circleAverage_eq_haar_circle]
  exact hresult

end SpringerLean

#print axioms SpringerLean.projectionAnalytic_circle_energy_first_mode
