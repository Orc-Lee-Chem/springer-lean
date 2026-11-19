import SpringerLean.Round1427AffineActiveEndpoints

namespace SpringerLean
set_option maxHeartbeats 200000

theorem refinedAffine_active_boundary_value
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    2-refinedAffineV W*refinedAffineActiveS W+
      (107/100:ℝ)*W^2 = 19/10 := by
  have hv : refinedAffineV W ≠ 0 := by
    dsimp [refinedAffineV]
    nlinarith
  unfold refinedAffineActiveS
  field_simp [hv]
  ring

/-- The entire model active arc maps to the affine branch. -/
theorem refinedAffine_profile_at_angle
    {W φ : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ refinedAffineBeta W) :
    refinedAffineRadius W
      (2*Real.cos (refinedAffineAngle (refinedAffineGamma W) φ)) =
      2*refinedAffineU W*Real.cos φ := by
  obtain ⟨_,_,hβ0,hβhalf,_,hβdef⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  obtain ⟨_,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < refinedAffineGamma W ∧ refinedAffineGamma W ≤ 1 at hγ
  have hβπ : refinedAffineBeta W ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    hφ0 hβπ hφ
  have hshort : 2-2*Real.cos φ ≤
      refinedAffineGamma W*(51/500:ℝ) := by
    have hβsmall : 2-2*Real.cos (refinedAffineBeta W) <
        refinedAffineGamma W*(51/500:ℝ) := by
      rw [hβdef]
      exact mul_lt_mul_of_pos_left hs hγ.1
    linarith
  have hangle := refinedAffine_angle_deficit hγ.1 hφ0
    (hφ.trans hβhalf) hshort
  have hU : 0 < refinedAffineU W := by
    dsimp [refinedAffineU]
    positivity
  have hbranch :
      2-(1-(107/100:ℝ)*W)*
        (2-2*Real.cos (refinedAffineAngle (refinedAffineGamma W) φ))+
        (107/100:ℝ)*W^2 = 2*refinedAffineU W*Real.cos φ := by
    have h := refinedAffine_branch_dilation W
      (2-2*Real.cos (refinedAffineAngle (refinedAffineGamma W) φ))
    rw [h]
    change refinedAffineU W *
      (2-refinedAffineGamma W *
        (2-2*Real.cos (refinedAffineAngle (refinedAffineGamma W) φ))) = _
    rw [hangle]
    ring
  have hboundary :
      refinedAffineU W*(2-(2-2*Real.cos (refinedAffineBeta W))) =
        (19/10:ℝ) := by
    rw [hβdef]
    have heq : refinedAffineU W*refinedAffineGamma W =
        refinedAffineV W := by
      unfold refinedAffineGamma
      field_simp [ne_of_gt hU]
    rw [mul_sub,← mul_assoc,heq]
    have h := refinedAffine_active_boundary_value hW0 hW
    dsimp [refinedAffineU] at *
    nlinarith
  have hactive : (19/10:ℝ) ≤ 2*refinedAffineU W*Real.cos φ := by
    have hh := mul_le_mul_of_nonneg_left
      (show 2-2*Real.cos (refinedAffineBeta W) ≥
        2-2*Real.cos φ by linarith) hU.le
    nlinarith [hboundary]
  unfold refinedAffineRadius
  rw [max_eq_right (by linarith [hbranch,hactive])]
  exact hbranch

/-- At and beyond the active transition, the 1.9 plateau is exact. -/
theorem refinedAffine_profile_platform
    {W θ : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hθα : refinedAffineAlpha W ≤ θ) (hθπ : θ ≤ Real.pi) :
    refinedAffineRadius W (2*Real.cos θ) = 19/10 := by
  obtain ⟨hα0,_,_,_,hαdef,_⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  have hv : 0 < refinedAffineV W := by
    dsimp [refinedAffineV]
    nlinarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    hα0 hθπ hθα
  have hs : refinedAffineActiveS W ≤ 2-2*Real.cos θ := by
    rw [← hαdef]
    linarith
  have hbranch :
      2-(1-(107/100:ℝ)*W)*(2-2*Real.cos θ)+
        (107/100:ℝ)*W^2 ≤ 19/10 := by
    have hh := mul_le_mul_of_nonneg_left hs hv.le
    have hboundary := refinedAffine_active_boundary_value hW0 hW
    dsimp [refinedAffineV] at *
    linarith
  unfold refinedAffineRadius
  exact max_eq_left hbranch

end SpringerLean

#print axioms SpringerLean.refinedAffine_profile_at_angle
#print axioms SpringerLean.refinedAffine_profile_platform
