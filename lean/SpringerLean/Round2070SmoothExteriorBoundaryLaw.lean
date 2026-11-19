import SpringerLean.Round2069ExteriorRadialGreenPotential
import SpringerLean.Round1964OddBoundaryProbability

open MeasureTheory Set Real Filter Metric
open scoped Topology

namespace SpringerLean

/-- The law on the smooth circle at source radius `s⁻¹`. -/
noncomputable def smoothExteriorBoundaryProbability (F : ℂ → ℂ) (s : ℝ) : Measure ℂ :=
  oddStarAngularProbability.map (fun θ => F (Complex.polarCoord.symm (s⁻¹, θ)))

private theorem smoothExterior_angle_norm (s : ℝ) (hs : 0 < s) (θ : ℝ) :
    ‖Complex.polarCoord.symm (s⁻¹, θ)‖ = s⁻¹ := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hs)]

theorem smoothExterior_angle_continuous
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Continuous (fun θ => F (Complex.polarCoord.symm (s⁻¹, θ))) := by
  apply hF.1.continuousOn.comp_continuous
  · simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  · intro θ
    change 1 < ‖Complex.polarCoord.symm (s⁻¹, θ)‖
    rw [smoothExterior_angle_norm s hs0]
    exact (one_lt_inv₀ hs0).mpr hs1

theorem smoothExteriorBoundaryProbability_univ
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    smoothExteriorBoundaryProbability F s univ = 1 := by
  unfold smoothExteriorBoundaryProbability
  rw [Measure.map_apply (smoothExterior_angle_continuous F hF s hs0 hs1).measurable
      MeasurableSet.univ, preimage_univ, oddStarAngularProbability_univ]

theorem smoothExteriorBoundaryProbability_ae_mem_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    exteriorOmittedAtScale F s ∈ ae (smoothExteriorBoundaryProbability F s) := by
  unfold smoothExteriorBoundaryProbability
  have hK := (exteriorOmittedAtScale_isCompact F hF hs0 hs1).measurableSet
  apply (ae_map_iff (smoothExterior_angle_continuous F hF s hs0 hs1).measurable.aemeasurable
    hK).mpr
  apply Eventually.of_forall
  intro θ
  let z : ℂ := Complex.polarCoord.symm (s⁻¹, θ)
  have hz : ‖z‖ = s⁻¹ := smoothExterior_angle_norm s hs0 θ
  have hsource : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  have hzd : z ∈ exteriorDisk := by
    change 1 < ‖z‖
    rw [hz]
    exact hsource
  change F z ∉ F '' exteriorAbove s⁻¹
  rintro ⟨w, hw, heq⟩
  have hw' : s⁻¹ < ‖w‖ := hw
  have hsame := hF.2.1 (hsource.trans hw') hzd heq
  rw [hsame, hz] at hw'
  exact (lt_irrefl _ hw')

theorem smoothExteriorBoundaryProbability_integral_eq_circleAverage
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (φ : ℂ → ℝ) (hφ : Measurable φ) :
    (∫ w, φ w ∂smoothExteriorBoundaryProbability F s) =
      circleAverage (fun z => φ (F z)) 0 s⁻¹ := by
  rw [smoothExteriorBoundaryProbability,
    integral_map (smoothExterior_angle_continuous F hF s hs0 hs1).measurable.aemeasurable
      hφ.aestronglyMeasurable, oddStarAngularProbability, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le), smul_eq_mul,
    circleAverage_eq_polar_setIntegral, oddStarAngularMeasure]

theorem smoothExteriorBoundaryProbability_log_potential_on_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : ℂ) (hx : x ∈ exteriorOmittedAtScale F s) :
    (∫ z, Real.log ‖z - x‖ ∂smoothExteriorBoundaryProbability F s) = -Real.log s := by
  rw [smoothExteriorBoundaryProbability_integral_eq_circleAverage
    F hF s hs0 hs1 _ (by fun_prop)]
  by_cases hximage : x ∈ F '' exteriorDisk
  · obtain ⟨w, hw, rfl⟩ := hximage
    have hle : ‖w‖ ≤ s⁻¹ := by
      by_contra! hlt
      exact hx ⟨w, hlt, rfl⟩
    rw [exterior_circle_log_potential_at_image F hF w hw s hs0 hs1, max_eq_left hle,
      Real.log_inv]
  · exact exterior_circle_log_potential_of_omitted F hF x hximage s hs0 hs1

theorem exteriorOmitted_subset_atScale
    (F : ℂ → ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    exteriorOmitted F ⊆ exteriorOmittedAtScale F s := by
  intro x hx
  change x ∉ F '' exteriorAbove s⁻¹
  rintro ⟨w, hw, rfl⟩
  exact hx ⟨w, ((one_lt_inv₀ hs0).mpr hs1).trans hw, rfl⟩

theorem exteriorOmittedAtScale_mono
    (F : ℂ → ℂ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    exteriorOmittedAtScale F t ⊆ exteriorOmittedAtScale F s := by
  intro x hx
  change x ∉ F '' exteriorAbove s⁻¹
  rintro ⟨w, hw, rfl⟩
  have hle : t⁻¹ ≤ s⁻¹ := inv_anti₀ hs hst
  exact hx ⟨w, hle.trans_lt hw, rfl⟩

theorem exteriorOmitted_eq_iInter_atScale (F : ℂ → ℂ) :
    exteriorOmitted F = ⋂ s ∈ Ioo (0 : ℝ) 1, exteriorOmittedAtScale F s := by
  ext x
  simp only [mem_iInter, mem_Ioo]
  constructor
  · intro hx s hs
    exact exteriorOmitted_subset_atScale F s hs.1 hs.2 hx
  · intro hx
    change x ∉ F '' exteriorDisk
    rintro ⟨w, hw, rfl⟩
    have hnorm : 1 < ‖w‖ := hw
    have hpositive : 0 < ‖w‖ := zero_lt_one.trans hnorm
    obtain ⟨s, hlow, hhigh⟩ := exists_between ((inv_lt_one₀ hpositive).mpr hnorm)
    have hs0 : 0 < s := (inv_pos.mpr hpositive).trans hlow
    have hs : s⁻¹ < ‖w‖ := by
      simpa only [inv_inv] using (inv_strictAnti₀ (inv_pos.mpr hpositive) hlow)
    exact hx s ⟨hs0, hhigh⟩ ⟨w, hs, rfl⟩

theorem smoothExteriorBoundaryProbability_boundedTest_tendsto
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (φ : BoundedContinuousFunction ℂ ℝ) :
    Tendsto (fun s : ℝ => ∫ z, φ z ∂smoothExteriorBoundaryProbability F s)
      (𝓝[<] (1 : ℝ)) (𝓝 (∫ z, φ z ∂actualExteriorBoundaryProbability F)) := by
  have hlim := (actualExteriorRadialTrace_boundedTest_integral_tendsto F hF φ).const_mul
    ((2 * Real.pi)⁻¹)
  have hactual :
      (∫ z, φ z ∂actualExteriorBoundaryProbability F) =
        (2 * Real.pi)⁻¹ * ∫ θ in Ioo (-Real.pi) Real.pi, φ (actualExteriorRadialTrace F θ) := by
    rw [actualExteriorBoundaryProbability, actualExteriorBoundaryMeasure,
      integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le),
      smul_eq_mul, integral_map (actualExteriorRadialTrace_aestronglyMeasurable F hF).aemeasurable
        φ.continuous.aestronglyMeasurable]
  rw [hactual]
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  rw [smoothExteriorBoundaryProbability_integral_eq_circleAverage
    F hF s hs.1 hs.2 _ φ.continuous.measurable, circleAverage_eq_polar_setIntegral]

end SpringerLean
