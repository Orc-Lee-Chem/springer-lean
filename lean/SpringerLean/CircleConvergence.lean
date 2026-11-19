import SpringerLean.CircleModeBridge

open scoped Topology NNReal

namespace SpringerLean

/-- The exact finite Fourier polynomials converge uniformly to the actual
derivative `F′` on every fixed exterior circle. -/
theorem exteriorDerivativePartialCircle_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) :
    TendstoUniformlyOn
      (fun M θ => exteriorDerivativePartialCircle F ρ M θ)
      (fun θ : AddCircle (2 * Real.pi) =>
        deriv F (exteriorCirclePoint ρ θ))
      Filter.atTop Set.univ := by
  have hρpos : 0 < ρ := by linarith
  have hrec : ρ⁻¹ < 1 := by
    have h := one_div_lt_one_div_of_lt
      (by norm_num : (0 : ℝ) < 1) hρ
    simpa only [one_div, inv_one] using h
  obtain ⟨r, hrec_r, hr1⟩ := exists_between hrec
  have hrnonneg : 0 ≤ r := le_trans (inv_nonneg.mpr hρpos.le) hrec_r.le
  let r' : ℝ≥0 := ⟨r, hrnonneg⟩
  have hbase := exteriorForwardGerm_deriv_uniform_on_subdisk F hc
    (r := r') hr1
  let invPoint : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => (exteriorCirclePoint ρ θ)⁻¹
  have hsubset : Set.univ ⊆
      invPoint ⁻¹' Metric.ball (0 : ℂ) r' := by
    intro θ hθ
    change invPoint θ ∈ Metric.ball (0 : ℂ) r'
    change dist (invPoint θ) 0 < (r' : ℝ)
    rw [dist_zero_right,
      show invPoint θ = (exteriorCirclePoint ρ θ)⁻¹ by rfl,
      norm_inv, exteriorCirclePoint_norm hρpos]
    exact hrec_r
  have hcircle := (hbase.comp invPoint).mono hsubset
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hcircle ε hε)]
    with M hM θ hθ
  let z := exteriorCirclePoint ρ θ
  have hz : z ∈ exteriorDisk :=
    exteriorCirclePoint_mem_exteriorDisk hρ θ
  have hznorm : ‖z‖ = ρ := exteriorCirclePoint_norm hρpos θ
  have hfactor : ‖(z ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_pow, hznorm]
    have hρsq : 1 ≤ ρ ^ 2 := by nlinarith
    exact inv_le_one_of_one_le₀ hρsq
  have hP := exteriorDerivativePartialCircle_eq_deriv_partial F ρ M θ
  have hF := exterior_deriv_eq_forwardGerm_deriv F hc hz
  have htail := hM θ hθ
  dsimp [invPoint] at htail
  change dist (deriv (exteriorForwardGerm F) z⁻¹)
    (∑ j ∈ Finset.range M,
      (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * (z⁻¹) ^ j) < ε at htail
  change dist (deriv F z) (exteriorDerivativePartialCircle F ρ M θ) < ε
  rw [dist_eq_norm] at htail
  rw [hF, hP, dist_eq_norm, norm_sub_rev]
  calc
    ‖(1 - (z ^ 2)⁻¹ *
          ∑ j ∈ Finset.range M,
            (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * (z⁻¹) ^ j) -
        (1 - (z ^ 2)⁻¹ * deriv (exteriorForwardGerm F) z⁻¹)‖ =
      ‖(z ^ 2)⁻¹‖ *
        ‖deriv (exteriorForwardGerm F) z⁻¹ -
          ∑ j ∈ Finset.range M,
            (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * (z⁻¹) ^ j‖ := by
      rw [← norm_mul]
      congr 1
      ring
    _ ≤ ‖deriv (exteriorForwardGerm F) z⁻¹ -
        ∑ j ∈ Finset.range M,
          (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * (z⁻¹) ^ j‖ := by
      exact mul_le_of_le_one_left (norm_nonneg _) hfactor
    _ < ε := htail

end SpringerLean
