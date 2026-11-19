import SpringerLean.AreaComparison

open Filter
open scoped Topology

namespace SpringerLean

/-- Elementary limit extraction from the explicit annulus comparison. -/
private theorem area_comparison_limit
    (B C K : ℝ) (A : ℝ → ℝ)
    (hA : Tendsto A atTop (𝓝 0))
    (hcomp : ∀ᶠ R : ℝ in atTop,
      (1 - B ^ 2 * (R⁻¹) ^ 4) *
        (R ^ 2 + K - A R) ≤
        (R + C * (R⁻¹) ^ 2) ^ 2) :
    K ≤ 0 := by
  let error : ℝ → ℝ := fun R =>
    A R + 2 * C * R⁻¹ + C ^ 2 * (R⁻¹) ^ 4 +
      B ^ 2 * (R⁻¹) ^ 2 +
        B ^ 2 * (R⁻¹) ^ 4 * (K - A R)
  have herror : Tendsto error atTop (𝓝 0) := by
    have hpair : Tendsto (fun R : ℝ => (R⁻¹, A R)) atTop (𝓝 (0, 0)) :=
      tendsto_inv_atTop_zero.prodMk_nhds hA
    have hcont : ContinuousAt
        (fun p : ℝ × ℝ =>
          p.2 + 2 * C * p.1 + C ^ 2 * p.1 ^ 4 +
            B ^ 2 * p.1 ^ 2 + B ^ 2 * p.1 ^ 4 * (K - p.2))
        (0, 0) := by fun_prop
    have h := hcont.tendsto.comp hpair
    simpa [error, Function.comp_def] using h
  have hle : ∀ᶠ R : ℝ in atTop, K ≤ error R := by
    filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
    have hR0 : R ≠ 0 := hRpos.ne'
    have hid :
        (R + C * (R⁻¹) ^ 2) ^ 2 -
          (1 - B ^ 2 * (R⁻¹) ^ 4) *
            (R ^ 2 + K - A R) = error R - K := by
      dsimp [error]
      field_simp [hR0]
      ring
    linarith
  exact ge_of_tendsto herror hle

/-- Letting only the outer circle tend to infinity gives the finite weighted
coefficient bound at each inner radius `r>1`. -/
theorem exteriorArea_finite_bound_at_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr : 1 < r) (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (r⁻¹) ^ (2 * j)) ≤ r ^ 2 := by
  let A : ℝ → ℝ := fun R =>
    ∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (R⁻¹) ^ (2 * j)
  let K : ℝ :=
    (∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (r⁻¹) ^ (2 * j)) - r ^ 2
  have hA : Tendsto A atTop (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.Icc 1 N : Finset ℕ)
      (f := fun (j : ℕ) (R : ℝ) =>
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
          (R⁻¹) ^ (2 * j))
      (a := fun (_ : ℕ) => (0 : ℝ))
      (by
        intro j hj
        have hjpos : 0 < 2 * j := by
          have := (Finset.mem_Icc.mp hj).1
          omega
        have hconst : Tendsto
            (fun _ : ℝ => (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2)
            atTop (𝓝 ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2)) :=
          tendsto_const_nhds
        have hpow : Tendsto
            (fun R : ℝ => (R⁻¹) ^ (2 * j))
            atTop (𝓝 ((0 : ℝ) ^ (2 * j))) :=
          (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow (2 * j)
        simpa [zero_pow (by omega : 2 * j ≠ 0)] using hconst.mul hpow)
    simpa [A] using hsum
  obtain ⟨C, R₀, hC, hrR₀, hcomparison⟩ :=
    exteriorArea_finite_comparison_real F hc hr N
  let B : ℝ := ‖exteriorForwardCoeff F 1‖
  have hcomp : ∀ᶠ R : ℝ in atTop,
      (1 - B ^ 2 * (R⁻¹) ^ 4) *
        (R ^ 2 + K - A R) ≤
        (R + C * (R⁻¹) ^ 2) ^ 2 := by
    filter_upwards [eventually_ge_atTop R₀] with R hR
    have hRpos : 0 < R := lt_trans (by linarith : 0 < r)
      (lt_of_lt_of_le hrR₀ hR)
    have hR0 : R ≠ 0 := hRpos.ne'
    have hratio :
        ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2 =
          B ^ 2 * (R⁻¹) ^ 4 := by
      rw [norm_div, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hRpos]
      dsimp [B]
      field_simp [hR0]
    have hsum :
        R ^ 2 - r ^ 2 +
          ∑ j ∈ Finset.Icc 1 N,
            (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
              ((r⁻¹) ^ (2 * j) - (R⁻¹) ^ (2 * j)) =
        R ^ 2 + K - A R := by
      dsimp [K, A]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    have hS : (R + C / R ^ 2) ^ 2 =
        (R + C * (R⁻¹) ^ 2) ^ 2 := by
      field_simp [hR0]
    have h := hcomparison R hR
    rw [hratio, hsum, hS] at h
    exact h
  have hK := area_comparison_limit B C K A hA hcomp
  dsimp [K] at hK
  linarith

end SpringerLean
