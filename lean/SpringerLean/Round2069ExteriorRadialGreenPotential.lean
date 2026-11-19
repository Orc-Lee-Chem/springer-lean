import SpringerLean.Round2068ExteriorBoundaryProbability
import SpringerLean.Round2046ExteriorJensen
import SpringerLean.Round12Compact

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace SpringerLean

/-- For an exterior test point, near-boundary smooth circles stay
uniformly separated from it. Use the open image of a more distant
exterior region and injectivity. -/
private theorem exteriorCircle_aeNear_separated_at_image
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (w : ℂ) (hw : w ∈ exteriorDisk) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ∀ θ : ℝ, δ ≤ ‖F (Complex.polarCoord.symm (r⁻¹,θ)) - F w‖ := by
  have hw' : 1 < ‖w‖ := hw
  let R := (1 + ‖w‖)/2
  have hR : 1 < R := by dsimp [R]; linarith
  have hRw : R < ‖w‖ := by dsimp [R]; linarith
  let U : Set ℂ := {z | R < ‖z‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hsub : U ⊆ exteriorDisk := fun z hz => hR.trans hz
  have himage := exterior_image_open_of_isOpen F hF hU hsub
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (himage.mem_nhds (show F w ∈ F '' U from ⟨w,hRw,rfl⟩))
  refine ⟨δ,hδ,?_⟩
  have hnear : (∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r⁻¹ < R) := by
    have hi : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] (1:ℝ)) (𝓝 1) := by
      simpa [Pi.inv_def] using (continuousAt_id.inv₀ (one_ne_zero : (1:ℝ) ≠ 0)).tendsto.mono_left
        (show 𝓝[<] (1:ℝ) ≤ 𝓝 (1:ℝ) from nhdsWithin_le_nhds)
    exact hi.eventually (gt_mem_nhds hR)
  filter_upwards [hnear,Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with r hrR hr θ
  let z : ℂ := Complex.polarCoord.symm (r⁻¹,θ)
  have hnorm : ‖z‖ = r⁻¹ := by
    dsimp [z]
    rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
  have hz : z ∈ exteriorDisk := by
    change 1 < ‖z‖
    rw [hnorm]
    exact (one_lt_inv₀ hr.1).mpr hr.2
  change δ ≤ ‖F z - F w‖
  by_contra! hlt
  have hFz : F z ∈ ball (F w) δ := by simpa only [mem_ball, dist_eq_norm] using hlt
  obtain ⟨u,hu,huF⟩ := hball hFz
  have huz := hF.2.1 (hsub hu) hz huF
  have hRu : R < ‖u‖ := hu
  rw [huz,hnorm] at hRu
  exact (not_lt_of_ge hrR.le) hRu

/-- The logarithmic potential of the actual radial probability at a
point in the exterior image is the exterior Green coordinate. This
uses domination away from the pole and does not assume equilibrium. -/
theorem actualExteriorBoundaryProbability_log_potential_at_image
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (w : ℂ) (hw : w ∈ exteriorDisk) :
    (∫ z, Real.log ‖z - F w‖ ∂actualExteriorBoundaryProbability F) = Real.log ‖w‖ := by
  let μ : Measure ℝ := volume.restrict (Ioo (-Real.pi) Real.pi)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [Real.volume_Ioo]
    finiteness)
  obtain ⟨δ,hδ,hsep⟩ := exteriorCircle_aeNear_separated_at_image F hF w hw
  let x := F w
  let ψ : ℂ → ℝ := fun z => Real.log ‖z-x‖
  have hψ : Measurable ψ := by dsimp [ψ]; fun_prop
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), AEStronglyMeasurable
      (fun θ => ψ (F (Complex.polarCoord.symm (r⁻¹,θ)))) μ := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with r hr
    have hc : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r⁻¹,θ)) := by
      simp_rw [Complex.polarCoord_symm_apply]
      fun_prop
    have hf := hF.1.continuousOn.comp_continuous hc (by
      intro θ
      change 1 < ‖Complex.polarCoord.symm (r⁻¹,θ)‖
      rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr.1)]
      exact (one_lt_inv₀ hr.1).mpr hr.2)
    exact (hψ.comp hf.measurable).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), ∀ᵐ θ ∂μ,
      ‖ψ (F (Complex.polarCoord.symm (r⁻¹,θ)))‖ ≤ |Real.log δ| + |Real.log (3+‖x‖)| := by
    filter_upwards [hsep,Ioo_mem_nhdsLT (by norm_num : (1/2:ℝ)<1)] with r hsep' hr
    apply Filter.Eventually.of_forall
    intro θ
    let z : ℂ := F (Complex.polarCoord.symm (r⁻¹,θ))
    have hr0 : 0 < r := by linarith [hr.1]
    have hri : r⁻¹ ≤ 2 := (inv_le_comm₀ hr0 (by norm_num : (0:ℝ)<2)).mpr (by
      norm_num; exact hr.1.le)
    have hz : ‖z‖ ≤ 3 := (exterior_polar_norm_le_radius_add_inv F hF hr0 hr.2 θ).trans
      (by linarith [hr.2])
    have hlo : δ ≤ ‖z-x‖ := hsep' θ
    have hhi : ‖z-x‖ ≤ 3+‖x‖ := (norm_sub_le _ _).trans (add_le_add hz le_rfl)
    have hl := Real.log_le_log hδ hlo
    have hh := Real.log_le_log (hδ.trans_le hlo) hhi
    change ‖Real.log ‖z-x‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [abs_nonneg (Real.log δ), neg_abs_le (Real.log δ),
      abs_nonneg (Real.log (3+‖x‖)), le_abs_self (Real.log (3+‖x‖))]
  have hpoint : ∀ᵐ θ ∂μ,
      Tendsto (fun r => ψ (F (Complex.polarCoord.symm (r⁻¹,θ))))
        (𝓝[<] (1:ℝ)) (𝓝 (ψ (actualExteriorRadialTrace F θ))) := by
    filter_upwards [actualExteriorRadialTrace_ae_tendsto F hF,
      actualExteriorRadialTrace_ae_mem_omitted F hF] with θ hθ hout
    have hdist : ‖actualExteriorRadialTrace F θ - x‖ ≠ 0 := by
      intro heq
      apply hout
      rw [sub_eq_zero.mp (norm_eq_zero.mp heq)]
      exact ⟨w,hw,rfl⟩
    exact (Real.continuousAt_log hdist).tendsto.comp (hθ.sub_const x).norm
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (fun _ : ℝ => |Real.log δ| + |Real.log (3+‖x‖)|) hmeas hbound
    (integrable_const _) hpoint
  have hlim' : Tendsto (fun r : ℝ => circleAverage (fun z => ψ (F z)) 0 r⁻¹)
      (𝓝[<] (1:ℝ)) (𝓝 (((2*π)⁻¹) * ∫ θ, ψ (actualExteriorRadialTrace F θ) ∂μ)) := by
    simpa only [circleAverage_eq_polar_setIntegral, μ] using hlim.const_mul (2*π)⁻¹
  have hconst : (fun r : ℝ => circleAverage (fun z => ψ (F z)) 0 r⁻¹) =ᶠ[𝓝[<] (1:ℝ)]
      (fun _ => Real.log ‖w‖) := by
    have hw' : 1 < ‖w‖ := hw
    have hi : Tendsto (fun r : ℝ => r⁻¹) (𝓝[<] (1:ℝ)) (𝓝 1) := by
      simpa [Pi.inv_def] using (continuousAt_id.inv₀ (one_ne_zero : (1:ℝ) ≠ 0)).tendsto.mono_left
        (show 𝓝[<] (1:ℝ) ≤ 𝓝 (1:ℝ) from nhdsWithin_le_nhds)
    filter_upwards [hi.eventually (gt_mem_nhds hw'), Ioo_mem_nhdsLT
      (by norm_num : (0:ℝ)<1)] with r hrw hr
    change circleAverage (fun z => Real.log ‖F z-F w‖) 0 r⁻¹ = _
    rw [exterior_circle_log_potential_at_image F hF w hw r hr.1 hr.2,
      max_eq_right hrw.le]
  have hEq := tendsto_nhds_unique (hlim'.congr' hconst) tendsto_const_nhds
  change (∫ z, ψ z ∂actualExteriorBoundaryProbability F) = _
  unfold actualExteriorBoundaryProbability actualExteriorBoundaryMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le),
    smul_eq_mul, integral_map
      (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable
      hψ.aestronglyMeasurable]
  exact hEq

end SpringerLean
