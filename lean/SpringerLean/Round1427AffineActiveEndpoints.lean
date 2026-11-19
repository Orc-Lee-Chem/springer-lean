import SpringerLean.Round1426AffineAngleSubstitution

namespace SpringerLean
set_option maxHeartbeats 200000

noncomputable def refinedAffineU (W : ℝ) : ℝ :=
  1+(107/200:ℝ)*W^2

noncomputable def refinedAffineV (W : ℝ) : ℝ :=
  1-(107/100:ℝ)*W

noncomputable def refinedAffineGamma (W : ℝ) : ℝ :=
  refinedAffineV W / refinedAffineU W

noncomputable def refinedAffineActiveS (W : ℝ) : ℝ :=
  ((1/10:ℝ)+(107/100:ℝ)*W^2)/refinedAffineV W

noncomputable def refinedAffineAlpha (W : ℝ) : ℝ :=
  Real.arccos (1-refinedAffineActiveS W/2)

noncomputable def refinedAffineBeta (W : ℝ) : ℝ :=
  Real.arccos (1-refinedAffineGamma W*refinedAffineActiveS W/2)

theorem refinedAffine_active_threshold_range
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    0 < refinedAffineActiveS W ∧
      refinedAffineActiveS W < 51/500 := by
  have hv : 0 < refinedAffineV W := by
    dsimp [refinedAffineV]
    nlinarith
  constructor
  · unfold refinedAffineActiveS
    exact div_pos (by positivity) hv
  · unfold refinedAffineActiveS
    apply (div_lt_iff₀ hv).2
    dsimp [refinedAffineV]
    have hsq : W^2 ≤ W/500 := by
      nlinarith [mul_nonneg hW0 (sub_nonneg.mpr hW)]
    nlinarith

theorem refinedAffine_active_endpoint_angles
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    0 ≤ refinedAffineAlpha W ∧
      refinedAffineAlpha W ≤ Real.pi/2 ∧
      0 ≤ refinedAffineBeta W ∧
      refinedAffineBeta W ≤ Real.pi/2 ∧
      2-2*Real.cos (refinedAffineAlpha W) = refinedAffineActiveS W ∧
      2-2*Real.cos (refinedAffineBeta W) =
        refinedAffineGamma W*refinedAffineActiveS W := by
  obtain ⟨hs0,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < refinedAffineGamma W ∧ refinedAffineGamma W ≤ 1 at hγ
  have hgs : 0 < refinedAffineGamma W*refinedAffineActiveS W :=
    mul_pos hγ.1 hs0
  have hgsLe : refinedAffineGamma W*refinedAffineActiveS W < 51/500 := by
    have hh := mul_le_mul_of_nonneg_right hγ.2 hs0.le
    nlinarith
  have hargA : 0 ≤ 1-refinedAffineActiveS W/2 ∧
      1-refinedAffineActiveS W/2 ≤ 1 := by constructor <;> linarith
  have hargB : 0 ≤ 1-refinedAffineGamma W*refinedAffineActiveS W/2 ∧
      1-refinedAffineGamma W*refinedAffineActiveS W/2 ≤ 1 := by
    constructor <;> linarith
  have hα0 : 0 ≤ refinedAffineAlpha W := Real.arccos_nonneg _
  have hβ0 : 0 ≤ refinedAffineBeta W := Real.arccos_nonneg _
  have hαhalf : refinedAffineAlpha W ≤ Real.pi/2 := by
    unfold refinedAffineAlpha
    have hh := Real.arccos_le_arccos hargA.1
    simpa using hh
  have hβhalf : refinedAffineBeta W ≤ Real.pi/2 := by
    unfold refinedAffineBeta
    have hh := Real.arccos_le_arccos hargB.1
    simpa using hh
  have hcosA : Real.cos (refinedAffineAlpha W) =
      1-refinedAffineActiveS W/2 := by
    unfold refinedAffineAlpha
    exact Real.cos_arccos (by linarith [hargA.1]) hargA.2
  have hcosB : Real.cos (refinedAffineBeta W) =
      1-refinedAffineGamma W*refinedAffineActiveS W/2 := by
    unfold refinedAffineBeta
    exact Real.cos_arccos (by linarith [hargB.1]) hargB.2
  exact ⟨hα0,hαhalf,hβ0,hβhalf,by rw [hcosA]; ring,
    by rw [hcosB]; ring⟩

/-- The inverse angle map takes the model active endpoint exactly to
the original affine-platform transition. -/
theorem refinedAffine_angle_beta_eq_alpha
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    refinedAffineAngle (refinedAffineGamma W) (refinedAffineBeta W) =
      refinedAffineAlpha W := by
  obtain ⟨hα0,hαhalf,hβ0,hβhalf,hαdef,hβdef⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  obtain ⟨hs0,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < refinedAffineGamma W ∧ refinedAffineGamma W ≤ 1 at hγ
  have hshort : 2-2*Real.cos (refinedAffineBeta W) ≤
      refinedAffineGamma W*(51/500:ℝ) := by
    rw [hβdef]
    exact mul_le_mul_of_nonneg_left hs.le hγ.1.le
  have hθrange := refinedAffine_angle_range hγ.1 hβ0 hβhalf hshort
  have hθdef := refinedAffine_angle_deficit hγ.1 hβ0 hβhalf hshort
  rw [hβdef] at hθdef
  have hdef : 2-2*Real.cos
      (refinedAffineAngle (refinedAffineGamma W) (refinedAffineBeta W)) =
      refinedAffineActiveS W := by
    exact (mul_left_cancel₀ (ne_of_gt hγ.1) hθdef)
  have hcos : Real.cos (refinedAffineAngle
      (refinedAffineGamma W) (refinedAffineBeta W)) =
      Real.cos (refinedAffineAlpha W) := by
    linarith
  have hθπ : refinedAffineAngle
      (refinedAffineGamma W) (refinedAffineBeta W) ≤ Real.pi := hθrange.2
  have hαπ : refinedAffineAlpha W ≤ Real.pi := by
    linarith [Real.pi_pos]
  calc
    refinedAffineAngle (refinedAffineGamma W) (refinedAffineBeta W) =
        Real.arccos (Real.cos (refinedAffineAngle
          (refinedAffineGamma W) (refinedAffineBeta W))) :=
      (Real.arccos_cos hθrange.1 hθπ).symm
    _ = Real.arccos (Real.cos (refinedAffineAlpha W)) := by rw [hcos]
    _ = refinedAffineAlpha W := Real.arccos_cos hα0 hαπ

end SpringerLean

#print axioms SpringerLean.refinedAffine_active_threshold_range
#print axioms SpringerLean.refinedAffine_angle_beta_eq_alpha
