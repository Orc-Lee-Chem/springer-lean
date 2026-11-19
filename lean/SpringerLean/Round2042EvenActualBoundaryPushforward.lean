import SpringerLean.Round2041EvenSmoothCirclePushforward
import SpringerLean.Round1861ActualTraceIntegrability

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem actualExteriorRadialTrace_boundedTest_integral_tendsto
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (φ : BoundedContinuousFunction ℂ ℝ) :
    Tendsto
      (fun r : ℝ => ∫ θ in Ioo (-Real.pi) Real.pi,
        φ (F (Complex.polarCoord.symm (r⁻¹,θ))))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ θ in Ioo (-Real.pi) Real.pi,
        φ (actualExteriorRadialTrace F θ))) := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r ∧ r < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    exact hr
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun θ : ℝ => φ (F (Complex.polarCoord.symm (r⁻¹,θ)))) μ := by
    filter_upwards [hnear] with r hr
    have hpolar : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r⁻¹,θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hmem (θ : ℝ) : Complex.polarCoord.symm (r⁻¹,θ) ∈ exteriorDisk := by
      change 1 < ‖Complex.polarCoord.symm (r⁻¹,θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
      exact (one_lt_inv₀ hr.1).2 hr.2
    exact (φ.continuous.comp (hF.1.continuousOn.comp_continuous hpolar hmem)).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ θ : ℝ ∂μ,
        ‖φ (F (Complex.polarCoord.symm (r⁻¹,θ)))‖ ≤ ‖φ‖ := by
    apply Filter.Eventually.of_forall
    intro r
    filter_upwards with θ
    exact BoundedContinuousFunction.norm_coe_le_norm φ _
  have hpoint : ∀ᵐ θ : ℝ ∂μ,
      Tendsto (fun r : ℝ => φ (F (Complex.polarCoord.symm (r⁻¹,θ))))
        (𝓝[<] (1 : ℝ)) (𝓝 (φ (actualExteriorRadialTrace F θ))) := by
    filter_upwards [actualExteriorRadialTrace_ae_tendsto F hF] with θ hθ
    exact φ.continuous.continuousAt.tendsto.comp hθ
  simpa only [μ] using
    tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (fun _ : ℝ => ‖φ‖) hmeas hbound (integrable_const _) hpoint

theorem evenPowerQuotient_actual_radial_integral_pushforward
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (φ : BoundedContinuousFunction ℂ ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      φ ((actualExteriorRadialTrace F θ)^k)) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (actualExteriorRadialTrace (evenExteriorPowerQuotient F k) θ) := by
  let G := evenExteriorPowerQuotient F k
  let ψ : BoundedContinuousFunction ℂ ℝ :=
    φ.compContinuous ⟨fun z : ℂ => z^k, by fun_prop⟩
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  have hlimF := actualExteriorRadialTrace_boundedTest_integral_tendsto F hF ψ
  have hlimG := actualExteriorRadialTrace_boundedTest_integral_tendsto G hG φ
  have hpow : Tendsto (fun r : ℝ => r^k)
      (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuousAt_pow (1 : ℝ) k).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
      exact pow_lt_one₀ hr.1.le hr.2 (by omega)
  have heq : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      (∫ θ in Ioo (-Real.pi) Real.pi,
        ψ (F (Complex.polarCoord.symm (r⁻¹,θ)))) =
      (∫ θ in Ioo (-Real.pi) Real.pi,
        φ (G (Complex.polarCoord.symm ((r^k)⁻¹,θ)))) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
    simpa [ψ, G, BoundedContinuousFunction.compContinuous_apply] using
      evenPowerQuotient_smooth_circle_integral_pushforward
        F K k hk hF hK hImage r hr.1 hr.2 φ φ.continuous
  have hsame := tendsto_nhds_unique (hlimF.congr' heq)
    (hlimG.comp hpow)
  simpa [ψ, G, BoundedContinuousFunction.compContinuous_apply] using hsame

noncomputable def actualExteriorBoundaryMeasure (F : ℂ → ℂ) : Measure ℂ :=
  (volume.restrict (Ioo (-Real.pi) Real.pi)).map (actualExteriorRadialTrace F)

theorem evenPowerQuotient_actual_boundary_measure_pushforward
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    (actualExteriorBoundaryMeasure F).map (fun z : ℂ => z^k) =
      actualExteriorBoundaryMeasure (evenExteriorPowerQuotient F k) := by
  let G := evenExteriorPowerQuotient F k
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have htraceF : AEMeasurable (actualExteriorRadialTrace F) μ :=
    (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  have htraceG : AEMeasurable (actualExteriorRadialTrace G) μ :=
    (actualExteriorRadialTrace_aestronglyMeasurable G hG).aemeasurable
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  haveI : IsFiniteMeasure (actualExteriorBoundaryMeasure F) :=
    Measure.isFiniteMeasure_map μ _
  haveI : IsFiniteMeasure ((actualExteriorBoundaryMeasure F).map
      (fun z : ℂ => z^k)) :=
    Measure.isFiniteMeasure_map (actualExteriorBoundaryMeasure F) _
  haveI : IsFiniteMeasure (actualExteriorBoundaryMeasure G) :=
    Measure.isFiniteMeasure_map μ _
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map (show AEMeasurable (fun z : ℂ => z^k)
      (actualExteriorBoundaryMeasure F) by fun_prop)
    φ.continuous.aestronglyMeasurable]
  rw [show (∫ z, φ (z^k) ∂actualExteriorBoundaryMeasure F) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ ((actualExteriorRadialTrace F θ)^k) by
      exact integral_map htraceF
        ((φ.continuous.comp (by fun_prop : Continuous (fun z : ℂ => z^k))).aestronglyMeasurable)]
  rw [show (∫ z, φ z ∂actualExteriorBoundaryMeasure G) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (actualExteriorRadialTrace G θ) by
      exact integral_map htraceG φ.continuous.aestronglyMeasurable]
  exact evenPowerQuotient_actual_radial_integral_pushforward
    F K k hk hF hK hImage φ

end SpringerLean
