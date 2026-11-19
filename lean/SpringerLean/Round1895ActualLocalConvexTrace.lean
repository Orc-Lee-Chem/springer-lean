import SpringerLean.Round1894LocalConvexSmooth
import SpringerLean.Round1861ActualTraceIntegrability

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

set_option maxHeartbeats 600000
set_option Elab.async false

/-- Convex order on the actual almost-everywhere radial trace.  The
smooth-circle comparison is passed through the same trace used in the
real moment statements. -/
theorem actualExteriorRadialTrace_localConvex_projection_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ (Set.Icc (-2) 2) ψ)
    (hψc : Continuous ψ) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in Ioo (-Real.pi) Real.pi,
        ψ ((conj ξ * actualExteriorRadialTrace F θ).re)) ≤
      Real.circleAverage (fun z : ℂ => ψ (2 * z.re)) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  obtain ⟨M, hM⟩ :=
    ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).image hψc).isBounded.exists_norm_le
  have hsnear : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s ∧ s < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
    exact hs
  have hsphere (s θ : ℝ) :
      rescaleExterior s F (Complex.polarCoord.symm (1, θ)) =
        (s : ℂ) * F (Complex.polarCoord.symm (s⁻¹, θ)) := by
    simp [rescaleExterior, div_eq_mul_inv, mul_comm]
  have hmeas : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun θ : ℝ => ψ ((conj ξ *
          rescaleExterior s F (Complex.polarCoord.symm (1, θ))).re)) μ := by
    filter_upwards [hsnear] with s hs
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (s⁻¹, θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hF : Continuous (fun θ : ℝ =>
        rescaleExterior s F (Complex.polarCoord.symm (1, θ))) := by
      have hF0 := hc.1.continuousOn.comp_continuous hp (by
        intro θ
        change 1 < ‖Complex.polarCoord.symm (s⁻¹, θ)‖
        rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hs.1)]
        exact (one_lt_inv₀ hs.1).mpr hs.2)
      have hh : Continuous (fun θ : ℝ =>
          (s : ℂ) * F (Complex.polarCoord.symm (s⁻¹, θ))) :=
        continuous_const.mul hF0
      simpa only [← hsphere] using hh
    exact (hψc.comp (Complex.continuous_re.comp
      (continuous_const.mul hF))).aestronglyMeasurable
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ : ℝ ∂μ,
        ‖ψ ((conj ξ * rescaleExterior s F
          (Complex.polarCoord.symm (1, θ))).re)‖ ≤ M := by
    filter_upwards [hsnear] with s hs
    filter_upwards with θ
    have hu : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by
      simp
    have hK := rescaleExterior_unitCircle_mem_omitted F hc hs.1 hs.2 hu
    have hn := exteriorOmitted_norm_le_two _
      (rescaleExterior_centeredExteriorUnivalent F hc hs.1 hs.2) hK
    have hr : (conj ξ * rescaleExterior s F
        (Complex.polarCoord.symm (1, θ))).re ∈ Icc (-2 : ℝ) 2 := by
      apply abs_le.mp
      calc
        _ ≤ ‖conj ξ * rescaleExterior s F
          (Complex.polarCoord.symm (1, θ))‖ := Complex.abs_re_le_norm _
        _ = ‖rescaleExterior s F
          (Complex.polarCoord.symm (1, θ))‖ := by
            rw [norm_mul, Complex.norm_conj, hξ, one_mul]
        _ ≤ 2 := hn
    exact hM _ ⟨_, hr, rfl⟩
  have hpoint : ∀ᵐ θ : ℝ ∂μ,
      Tendsto
        (fun s : ℝ => ψ ((conj ξ * rescaleExterior s F
          (Complex.polarCoord.symm (1, θ))).re))
        (𝓝[<] (1 : ℝ))
        (𝓝 (ψ ((conj ξ * actualExteriorRadialTrace F θ).re))) := by
    filter_upwards [actualExteriorRadialTrace_ae_tendsto F hc] with θ hθ
    have hs : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hprod := hs.mul hθ
    have hlim : Tendsto
        (fun s : ℝ => rescaleExterior s F (Complex.polarCoord.symm (1, θ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (actualExteriorRadialTrace F θ)) := by
      simpa only [hsphere, one_mul] using hprod
    exact hψc.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_const_nhds.mul hlim))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun _ : ℝ => M) hmeas hbound (integrable_const _) hpoint
  have hlim' : Tendsto
      (fun s : ℝ => Real.circleAverage
        (fun z : ℂ => ψ ((conj ξ * rescaleExterior s F z).re)) 0 1)
      (𝓝[<] (1 : ℝ))
      (𝓝 ((2 * Real.pi)⁻¹ *
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ψ ((conj ξ * actualExteriorRadialTrace F θ).re))) := by
    simpa only [circleAverage_eq_polar_setIntegral, μ] using
      hlim.const_mul ((2 * Real.pi)⁻¹)
  apply le_of_tendsto_of_tendsto hlim' tendsto_const_nhds
  filter_upwards [hsnear] with s hs
  exact regularExterior_localConvex_boundary_le F hc hs.1 hs.2 ξ hξ ψ hψ hψc

/-- The normalized projection used in real-exponent interpolation is
convexly dominated by the cosine law on the unit circle. -/
theorem actualExteriorRadialTrace_half_projection_localConvex_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Set.Icc (-1) 1) φ)
    (hφc : Continuous φ) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in Ioo (-Real.pi) Real.pi,
        φ ((conj ξ * actualExteriorRadialTrace F θ).re / 2)) ≤
      Real.circleAverage (fun z : ℂ => φ z.re) 0 1 := by
  have hconv : ConvexOn ℝ (Set.Icc (-2) 2) (fun x : ℝ => φ (x / 2)) := by
    refine ⟨convex_Icc (-2 : ℝ) 2, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxu : x / 2 ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    have hyu : y / 2 ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [hy.1, hy.2]
    simpa only [smul_eq_mul, add_div, mul_div_assoc] using
      hφ.2 hxu hyu ha hb hab
  have h := actualExteriorRadialTrace_localConvex_projection_le F hc ξ hξ
    (fun x : ℝ => φ (x / 2)) hconv (hφc.comp (continuous_id.div_const 2))
  simpa only [show ∀ z : ℂ, (2 * z.re) / 2 = z.re from
    fun z => by ring] using h

end SpringerLean

#check @SpringerLean.actualExteriorRadialTrace_localConvex_projection_le
#print axioms SpringerLean.actualExteriorRadialTrace_localConvex_projection_le
#check @SpringerLean.actualExteriorRadialTrace_half_projection_localConvex_le
#print axioms SpringerLean.actualExteriorRadialTrace_half_projection_localConvex_le
