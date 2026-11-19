import SpringerLean.Round2042EvenActualBoundaryPushforward
import SpringerLean.Round2029ExteriorMapUniqueness

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean

/-- The actual angular radial law, normalized to total mass one. -/
noncomputable def actualExteriorBoundaryProbability (F : ℂ → ℂ) : Measure ℂ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • actualExteriorBoundaryMeasure F

theorem actualExteriorBoundaryProbability_univ
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) :
    actualExteriorBoundaryProbability F univ = 1 := by
  unfold actualExteriorBoundaryProbability actualExteriorBoundaryMeasure
  rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable
      (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
  have hπ : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [hπ]
  change ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * Real.pi) = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le), inv_mul_cancel₀ Real.two_pi_pos.ne']
  exact ENNReal.ofReal_one

/-- Almost every actual radial limit belongs to the omitted set.
An exterior image point would give a limit of the inverse at an
exterior point, although the original inverse coordinates tend to
the unit circle. -/
theorem actualExteriorRadialTrace_ae_mem_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) :
    ∀ᵐ θ ∂(volume.restrict (Ioo (-Real.pi) Real.pi)),
      actualExteriorRadialTrace F θ ∉ F '' exteriorDisk := by
  filter_upwards [actualExteriorRadialTrace_ae_tendsto F hF] with θ hθ
  rintro ⟨w, hw, hval⟩
  let z (r : ℝ) := (Complex.polarCoord.symm (r⁻¹,θ) : ℂ)
  have hc := (exteriorInverse_analyticAt_image F hF w hw).continuousAt
  have hθ' : Tendsto (fun r => F (z r)) (𝓝[<] (1:ℝ)) (𝓝 (F w)) := hval.symm ▸ hθ
  have hlimit : Tendsto (fun r => exteriorInverse F (F (z r))) (𝓝[<] (1:ℝ)) (𝓝 w) := by
    have h := hc.tendsto.comp hθ'
    have hi : exteriorInverse F (F w) = w := hF.2.1.leftInvOn_invFunOn hw
    simpa only [Function.comp_def, hi] using h
  have hEq : (fun r => exteriorInverse F (F (z r))) =ᶠ[𝓝[<] (1:ℝ)] z := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with r hr
    have hz : z r ∈ exteriorDisk := by
      change 1 < ‖Complex.polarCoord.symm (r⁻¹,θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
      exact (one_lt_inv₀ hr.1).mpr hr.2
    exact hF.2.1.leftInvOn_invFunOn hz
  have hznorm : Tendsto (fun r => ‖z r‖) (𝓝[<] (1:ℝ)) (𝓝 1) := by
    have hi : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] (1:ℝ)) (𝓝 1) := by
      simpa [Pi.inv_def] using (continuousAt_id.inv₀ (one_ne_zero : (1:ℝ) ≠ 0)).tendsto.mono_left
        (show 𝓝[<] (1:ℝ) ≤ 𝓝 (1:ℝ) from nhdsWithin_le_nhds)
    apply hi.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with r hr
    change r⁻¹ = ‖Complex.polarCoord.symm (r⁻¹,θ)‖
    rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
  have hnorm : ‖w‖ = 1 := tendsto_nhds_unique (hlimit.congr' hEq).norm hznorm
  exact (ne_of_gt hw) hnorm

theorem actualExteriorBoundaryProbability_ae_mem_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hK : IsClosed (F '' exteriorDisk)ᶜ) :
    (F '' exteriorDisk)ᶜ ∈ ae (actualExteriorBoundaryProbability F) := by
  have ht := (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable
  unfold actualExteriorBoundaryProbability actualExteriorBoundaryMeasure
  apply Filter.Eventually.filter_mono (Measure.ae_mono' Measure.smul_absolutelyContinuous)
  exact (ae_map_iff ht hK.measurableSet).mpr
    (actualExteriorRadialTrace_ae_mem_omitted F hF)

end SpringerLean
