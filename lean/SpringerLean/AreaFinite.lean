import SpringerLean.AreaLimit

open Filter
open scoped Topology

namespace SpringerLean

/-- The finite exterior area theorem, directly from the paper's original
centered univalent function class and the derivative-defined coefficients. -/
theorem exteriorForwardCoeff_finite_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (N : ℕ) :
    (∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤ 1 := by
  let S : ℝ → ℝ := fun r =>
    ∑ j ∈ Finset.Icc 1 N,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2 *
        (r⁻¹) ^ (2 * j)
  have hcont : ContinuousAt S 1 := by
    dsimp [S]
    fun_prop (disch := norm_num)
  have hfilter : (𝓝[>] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) :=
    nhdsWithin_le_nhds
  have hlimS : Tendsto S (𝓝[>] (1 : ℝ))
      (𝓝 (∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2)) := by
    have h := hcont.tendsto.mono_left hfilter
    simpa [S] using h
  have hlimR : Tendsto (fun r : ℝ => r ^ 2)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_id.mono_left hfilter).pow 2)
  have hbound : ∀ᶠ r : ℝ in 𝓝[>] (1 : ℝ), S r ≤ r ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact exteriorArea_finite_bound_at_radius F hc hr N
  exact le_of_tendsto_of_tendsto hlimS hlimR hbound

end SpringerLean
