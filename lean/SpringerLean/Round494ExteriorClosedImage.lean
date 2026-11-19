import SpringerLean.ForwardBound
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace SpringerLean
set_option Elab.async false

/-- The restriction to any closed source exterior of radius greater than one
is proper. This uses the actual normalization, without any boundary extension. -/
theorem exterior_closed_restriction_isProper
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {r : ℝ} (hr : 1 < r) :
    IsProperMap (fun z : {z : ℂ | r ≤ ‖z‖} => F z) := by
  let S : Set ℂ := {z | r ≤ ‖z‖}
  have hS : IsClosed S := isClosed_le continuous_const continuous_norm
  have hSE : S ⊆ exteriorDisk := fun z hz => lt_of_lt_of_le hr hz
  have hF : ContinuousOn F S := hc.1.continuousOn.mono hSE
  obtain ⟨C, hC, hg⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  have hbound (z : ℂ) (hz : z ∈ S) : ‖z‖ ≤ ‖F z‖ + C := by
    have hzE := hSE hz
    have hz0 := exterior_ne_zero hzE
    have hz1 : 1 < ‖z‖ := hzE
    have hzi : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]
      exact (inv_lt_one₀ (by positivity : 0 < ‖z‖)).mpr hz1
    have htail := hg z⁻¹ hzi
    rw [exteriorForwardGerm_punctured F (inv_ne_zero hz0), inv_inv] at htail
    have hn := norm_sub_le (F z) (F z - z)
    have he : F z - (F z - z) = z := by ring
    rw [he] at hn
    linarith
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuousOn_iff_continuous_domRestrict.mp hF, ?_⟩
  intro K hK
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hclosed : IsClosed (S ∩ F ⁻¹' K) := hF.preimage_isClosed_of_isClosed hS hK.isClosed
  have hsub : S ∩ F ⁻¹' K ⊆ Metric.closedBall (0 : ℂ) (M + C) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hbound z hz.1, hM _ hz.2]
  have hk : IsCompact (S ∩ F ⁻¹' K) :=
    (isCompact_closedBall (0 : ℂ) (M + C)).of_isClosed_subset hclosed hsub
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert hk using 1
  ext z
  simp [S, and_comm]

theorem exterior_closed_image_isClosed
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {r : ℝ} (hr : 1 < r) :
    IsClosed (F '' {z : ℂ | r ≤ ‖z‖}) := by
  have hp := exterior_closed_restriction_isProper F hc hr
  have h := hp.isClosedMap Set.univ isClosed_univ
  convert h using 1
  ext w
  simp

end SpringerLean
