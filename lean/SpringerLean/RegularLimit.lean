import SpringerLean.ForwardBound

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The regular correction derivative has the exponent `s²`, not `s`. -/
theorem regularForwardGerm_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (_hs : 0 < s) {u : ℂ}
    (hu : ‖(s : ℂ) * u‖ < 1) :
    deriv (regularForwardGerm s F) u =
      (s : ℂ) ^ 2 * deriv (exteriorForwardGerm F) ((s : ℂ) * u) := by
  have harg : (s : ℂ) * u ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hf : HasDerivAt (exteriorForwardGerm F)
      (deriv (exteriorForwardGerm F) ((s : ℂ) * u)) ((s : ℂ) * u) :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) _ harg).differentiableAt.hasDerivAt
  have hinner : HasDerivAt (fun v : ℂ => (s : ℂ) * v) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).const_mul (s : ℂ)
  have hcomp := hf.comp u hinner
  have hout := hcomp.const_mul (s : ℂ)
  have hder : deriv (regularForwardGerm s F) u =
      (s : ℂ) * (deriv (exteriorForwardGerm F) ((s : ℂ) * u) * (s : ℂ)) := by
    change deriv (fun y : ℂ =>
      (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * y)) u = _
    simpa only [Function.comp_def] using hout.deriv
  rw [hder]
  ring

/-- A single bound works for all regular harmonic fillings, every
`0<s<1`, and every point in the open disk. -/
theorem regularHarmonic_uniform_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ), 0 < s → s < 1 →
        ∀ z : ℂ, ‖z‖ < 1 → ‖regularHarmonic s F z‖ ≤ C := by
  obtain ⟨B, hBnonneg, hB⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  refine ⟨1 + B, by linarith, ?_⟩
  intro s hs0 hs1 z hz
  have hsu : ‖(s : ℂ) * conj z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hznorm : ‖conj z‖ = ‖z‖ := by
      simpa only [← Complex.star_def] using norm_star z
    rw [hznorm]
    nlinarith [mul_nonneg (le_of_lt hs0) (norm_nonneg z)]
  have hsle : s ≤ 1 := hs1.le
  calc
    ‖regularHarmonic s F z‖ =
        ‖z + (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * conj z)‖ := rfl
    _ ≤ ‖z‖ + ‖(s : ℂ) * exteriorForwardGerm F ((s : ℂ) * conj z)‖ :=
      norm_add_le _ _
    _ = ‖z‖ + s * ‖exteriorForwardGerm F ((s : ℂ) * conj z)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    _ ≤ 1 + B := by
      have hgb := hB _ hsu
      nlinarith [mul_nonneg (le_of_lt hs0) (sub_nonneg.mpr hgb)]

/-- At every interior point, the regular correction tends to the actual
forward correction as `s` approaches one from below. -/
theorem regularForwardGerm_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {u : ℂ} (hu : ‖u‖ < 1) :
    Tendsto (fun s : ℝ => regularForwardGerm s F u)
      (𝓝[<] (1 : ℝ)) (𝓝 (exteriorForwardGerm F u)) := by
  have hlim : Tendsto (fun s : ℝ => s)
      (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hreal : Tendsto (fun s : ℝ => (s : ℂ))
      (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hlim)
  have harg : u ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hgcont :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) u harg).continuousAt
  have hsu : Tendsto (fun s : ℝ => (s : ℂ) * u)
      (𝓝[<] (1 : ℝ)) (𝓝 u) := by
    simpa only [one_mul] using hreal.mul (tendsto_const_nhds (x := u))
  have hcomp := hgcont.tendsto.comp hsu
  have hprod : Tendsto
      (fun s : ℝ => (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * u))
      (𝓝[<] (1 : ℝ))
      (𝓝 ((1 : ℂ) * exteriorForwardGerm F u)) :=
    hreal.mul hcomp
  simpa only [regularForwardGerm, one_mul] using hprod

/-- Pointwise convergence of the actual harmonic fillings inside the disk. -/
theorem regularHarmonic_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun s : ℝ => regularHarmonic s F z)
      (𝓝[<] (1 : ℝ))
      (𝓝 (z + exteriorForwardGerm F (conj z))) := by
  have hzc : ‖conj z‖ < 1 := by
    simpa only [← Complex.star_def, norm_star] using hz
  simpa only [regularHarmonic] using
    (tendsto_const_nhds.add (regularForwardGerm_tendsto F hc hzc))

end SpringerLean
