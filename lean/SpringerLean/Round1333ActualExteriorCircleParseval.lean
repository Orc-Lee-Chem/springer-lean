import SpringerLean.Round1332ActualCirclePartial
import SpringerLean.Round1317RadialTwoSummable

open MeasureTheory AddCircle Filter Metric

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- On every actual exterior circle, the map is its leading mode plus
the original forward germ evaluated at the reciprocal circle point. -/
theorem exteriorCirclePoint_actual_forwardGerm
    (F : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (θ : AddCircle (2 * Real.pi)) :
    F (exteriorCirclePoint ρ θ) =
      exteriorCirclePoint ρ θ +
        exteriorForwardGerm F ((exteriorCirclePoint ρ θ)⁻¹) := by
  have hz : exteriorCirclePoint ρ θ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [exteriorCirclePoint_norm hρ θ]
    exact ne_of_gt hρ
  rw [exteriorForwardGerm_punctured F (inv_ne_zero hz)]
  simp

/-- The actual finite exterior Fourier truncations converge uniformly
on any fixed exterior circle to the original map. -/
theorem finiteExteriorFourierPartial_actual_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun M θ => finiteExteriorFourierPartial
        (exteriorForwardCoeff F) r M θ)
      (fun θ : AddCircle (2 * Real.pi) =>
        F (exteriorCirclePoint r⁻¹ θ)) atTop Set.univ := by
  have hρ : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  let Rnn : NNReal := ⟨R, by linarith⟩
  have hrun : (Rnn : ℝ) < 1 := hR1
  have hsource := exteriorForwardGerm_uniform_on_subdisk F hc (r := Rnn) hrun
  let point : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => (exteriorCirclePoint r⁻¹ θ)⁻¹
  have hnorm (θ : AddCircle (2 * Real.pi)) : ‖point θ‖ = r := by
    dsimp [point]
    rw [norm_inv, exteriorCirclePoint_norm (by positivity : 0 < r⁻¹) θ]
    simp
  have hmap : Set.univ ⊆ point ⁻¹' ball (0 : ℂ) R := by
    intro θ hθ
    rw [Set.mem_preimage, mem_ball, dist_zero_right, hnorm]
    exact hrR
  have hu := (hsource.comp point).mono hmap
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with M hM θ hθ
  have hp := finiteExteriorFourierPartial_actual_eq F r M θ
  have hq := exteriorCirclePoint_actual_forwardGerm F
    (by positivity : 0 < r⁻¹) θ
  simpa only [Function.comp_apply, point, hp, hq, dist_add_left,
    dist_comm] using hM θ (Set.mem_univ θ)

/-- Actual exterior-circle Parseval, stated as the convergence of the
finite coefficient energies to the circle mean of the original `F`.
The boundary limit `r ↑ 1` is a separate theorem. -/
theorem exterior_actual_circle_two_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto
      (fun M => (r⁻¹) ^ 2 +
        ∑ j ∈ Finset.range M,
          ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j))
      atTop
      (nhds (Real.circleAverage (fun z : ℂ => ‖F z‖ ^ 2) 0 r⁻¹)) := by
  let p : ℕ → AddCircle (2 * Real.pi) → ℂ :=
    fun M θ => finiteExteriorFourierPartial (exteriorForwardCoeff F) r M θ
  let q : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => F (exteriorCirclePoint r⁻¹ θ)
  have hp : ∀ M, Continuous (p M) := by
    intro M
    dsimp [p, finiteExteriorFourierPartial, finiteFourierFamily]
    fun_prop
  have hρ : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  have hq : Continuous q := by
    have hpoint : Continuous (exteriorCirclePoint r⁻¹) := by
      unfold exteriorCirclePoint
      fun_prop
    exact hc.1.continuousOn.comp_continuous hpoint
      (fun θ => exteriorCirclePoint_mem_exteriorDisk hρ θ)
  have hu := finiteExteriorFourierPartial_actual_uniform F hc hr0 hr1
  have hlim := circle_energy_tendsto_of_uniform p q hp hq hu
  have hfinite (M : ℕ) :
      (∫ θ : AddCircle (2 * Real.pi), ‖p M θ‖ ^ 2 ∂haarAddCircle) =
        (r⁻¹) ^ 2 +
          ∑ j ∈ Finset.range M,
            ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j) :=
    finiteExteriorFourierPartial_energy _ r hr0 M
  have hactual :
      (∫ θ : AddCircle (2 * Real.pi), ‖q θ‖ ^ 2 ∂haarAddCircle) =
        Real.circleAverage (fun z : ℂ => ‖F z‖ ^ 2) 0 r⁻¹ :=
    (circleAverage_eq_haar_circle (fun z : ℂ => ‖F z‖ ^ 2) r⁻¹).symm
  simpa only [hfinite, hactual] using hlim

/-- Exact Parseval for the actual map on every exterior circle.  The
remaining p=2 bridge is the `ρ ↓ 1` passage to its a.e. radial trace. -/
theorem exterior_actual_circle_two_energy_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖F z‖ ^ 2) 0 r⁻¹ =
      (r⁻¹) ^ 2 +
        ∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j) := by
  have hs : Summable (fun j : ℕ =>
      ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j)) := by
    apply Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => ?_) (exteriorForwardCoeff_sq_summable F hc)
    have hpow : r ^ (2 * j) ≤ 1 := pow_le_one₀ hr0.le hr1.le
    exact mul_le_of_le_one_right (sq_nonneg _) hpow
  have hsum := hs.hasSum.tendsto_sum_nat.const_add ((r⁻¹) ^ 2)
  have hactual := exterior_actual_circle_two_energy_tendsto F hc hr0 hr1
  exact tendsto_nhds_unique hactual hsum

/-- The same actual-map Parseval identity in the paper's exterior radius
parameter `ρ>1`. -/
theorem exterior_actual_rho_circle_two_parseval
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) :
    Real.circleAverage (fun z : ℂ => ‖F z‖ ^ 2) 0 ρ =
      ρ ^ 2 +
        ∑' j : ℕ, ‖exteriorForwardCoeff F j‖ ^ 2 *
          (ρ⁻¹) ^ (2 * j) := by
  have hρ0 : 0 < ρ := by linarith
  have hr0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hr1 : ρ⁻¹ < 1 := by
    apply (inv_lt_one₀ hρ0).2
    exact hρ
  simpa only [inv_inv] using
    (exterior_actual_circle_two_energy_eq F hc hr0 hr1)

end SpringerLean

#print axioms SpringerLean.exterior_actual_circle_two_energy_tendsto
#print axioms SpringerLean.exterior_actual_rho_circle_two_parseval
