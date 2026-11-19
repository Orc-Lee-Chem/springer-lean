import SpringerLean.Round2080SmoothFactorLowerBound
import SpringerLean.Round480OmittedRadius

open MeasureTheory Set Filter Real
open scoped Topology

namespace SpringerLean

/-- For two distinct points of a compact set, half their distance is
a uniform positive lower bound for the farthest-point distance. -/
theorem half_norm_sub_le_continuumFarthestDistance (K : Set ℂ) (hK : IsCompact K)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (z : ℂ) :
    ‖u-v‖ / 2 ≤ continuumFarthestDistance K z := by
  have hu' := continuumFarthestDistance_ge_distance K hK z u hu
  have hv' := continuumFarthestDistance_ge_distance K hK z v hv
  have h := norm_sub_le (u-z) (v-z)
  rw [show (u-z)-(v-z) = u-v by ring, norm_sub_rev u z, norm_sub_rev v z] at h
  linarith

/-- Passing the sampled-polynomial lower bound to the actual radial
law for every admissible factor constant. -/
theorem factorInequality_log_ge_actual_farthest
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (hne : u ≠ v)
    (c : ℝ) (hc : FactorInequality (exteriorOmitted F) c) :
    (∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
      ∂actualExteriorBoundaryProbability F) ≤ Real.log c := by
  let K := exteriorOmitted F
  let μ := actualExteriorBoundaryProbability F
  let d := continuumFarthestDistance K
  let δ := min (‖u-v‖ / 2) 1
  have hK := exteriorOmitted_isCompact F hF
  have hKne : K.Nonempty := ⟨u, hu⟩
  have hδ : 0 < δ := lt_min (half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) zero_lt_one
  have hδd (z : ℂ) : δ ≤ d z :=
    (min_le_left _ _).trans (half_norm_sub_le_continuumFarthestDistance K hK u v hu hv z)
  have hδ5 : δ ≤ 5 := (min_le_right _ _).trans (by norm_num)
  have hbd (z : ℂ) (hz : ‖z‖ ≤ 3) : d z ≤ 5 := by
    obtain ⟨w,hw,he⟩ := continuumFarthestDistance_eq_distance_at_max K hK hKne z
    change d z = _ at he
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith [exteriorOmitted_norm_le_two F hF hw])
  have hdc : Continuous d := continuumFarthestDistance_continuous K hK hKne
  let f (z : ℂ) := Real.log (min 5 (d z))
  have hf : Continuous f :=
    (continuous_const.min hdc).log (fun z => (hδ.trans_le (le_min hδ5 (hδd z))).ne')
  have hfBounds (z : ℂ) : Real.log δ ≤ f z ∧ f z ≤ Real.log 5 := by
    have h := le_min hδ5 (hδd z)
    exact ⟨Real.log_le_log hδ h, Real.log_le_log (hδ.trans_le h) (min_le_left _ _)⟩
  let φ : BoundedContinuousFunction ℂ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ (Real.log 5 - Real.log δ) (by
      intro x y
      change |f x-f y| ≤ _
      rw [abs_le]
      constructor <;> linarith [(hfBounds x).1, (hfBounds x).2, (hfBounds y).1, (hfBounds y).2])
  have hφ (z : ℂ) (hz : ‖z‖ ≤ 3) : φ z = Real.log (d z) := by
    change Real.log (min 5 (d z)) = _
    rw [min_eq_right (hbd z hz)]
  have hν : K ∈ ae μ :=
    actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
  have hlast : (∫ z, φ z ∂μ) = ∫ z, Real.log (d z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hν] with z hz
    exact hφ z ((exteriorOmitted_norm_le_two F hF hz).trans (by norm_num))
  have hlim := smoothExteriorBoundaryProbability_boundedTest_tendsto F hF φ
  change Tendsto (fun s => ∫ z, φ z ∂smoothExteriorBoundaryProbability F s)
    (𝓝[<] (1:ℝ)) (𝓝 (∫ z, φ z ∂μ)) at hlim
  have hlog : Tendsto Real.log (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.log_one] using (Real.continuousAt_log (one_ne_zero : (1:ℝ) ≠ 0)).tendsto.mono_left
      (show 𝓝[<] (1:ℝ) ≤ 𝓝 (1:ℝ) from nhdsWithin_le_nhds)
  have hsum : Tendsto (fun s => (∫ z, φ z ∂smoothExteriorBoundaryProbability F s) + Real.log s)
      (𝓝[<] (1:ℝ)) (𝓝 (∫ z, Real.log (d z) ∂μ)) := by
    simpa only [add_zero, hlast] using hlim.add hlog
  apply le_of_tendsto hsum
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1/2:ℝ)<1)] with s hs
  have hs0 : 0 < s := (by norm_num : (0:ℝ)<1/2).trans hs.1
  have hi : s⁻¹ ≤ 2 := (inv_anti₀ (by norm_num : (0:ℝ)<1/2) hs.1.le).trans_eq
    (by norm_num)
  have hsupp : ∀ᵐ z ∂smoothExteriorBoundaryProbability F s, ‖z‖ ≤ 3 := by
    unfold smoothExteriorBoundaryProbability
    rw [ae_map_iff (smoothExterior_angle_continuous F hF s hs0 hs.2).measurable.aemeasurable]
    · filter_upwards with θ
      have hnorm := exterior_polar_norm_le_radius_add_inv F hF hs0 hs.2 θ
      linarith [hs.2]
    · exact (isClosed_le continuous_norm continuous_const).measurableSet
  have heq : (∫ z, φ z ∂smoothExteriorBoundaryProbability F s) =
      ∫ z, Real.log (d z) ∂smoothExteriorBoundaryProbability F s :=
    integral_congr_ae (hsupp.mono hφ)
  rw [heq]
  exact factorInequality_log_ge_smooth_farthest F hF u v hu hv hne c hc s hs0 hs.2

end SpringerLean
