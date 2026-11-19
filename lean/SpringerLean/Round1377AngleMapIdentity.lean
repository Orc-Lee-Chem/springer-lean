import SpringerLean.Round1376AngleMapBasics

namespace SpringerLean

theorem coarseAnglePhi_zero : coarseAnglePhi 0 = 0 := by
  simp [coarseAnglePhi, coarseAngleArgument, coarseAngleDeficit]

theorem coarseAnglePhi_range
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    0 ≤ coarseAnglePhi v ∧ coarseAnglePhi v ≤ Real.pi := by
  obtain ⟨hu0,_⟩ := coarseAngleArgument_range hv0 hvβ
  unfold coarseAnglePhi
  constructor
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.2 hu0)
  · linarith [Real.arcsin_le_pi_div_two (coarseAngleArgument v)]

/-- The angle map removes the quadratic projection loss exactly. -/
theorem coarseAnglePhi_deficit
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    2-2*Real.cos (coarseAnglePhi v) =
      coarseAngleDeficit v+5*coarseAngleDeficit v^2 := by
  let u : ℝ := coarseAngleArgument v
  obtain ⟨hu0,hu8⟩ := coarseAngleArgument_range hv0 hvβ
  have hsin : Real.sin (Real.arcsin u) = u :=
    Real.sin_arcsin (by dsimp [u] at *; linarith) (by dsimp [u] at *; linarith)
  have htrig := Real.sin_sq_add_cos_sq (Real.arcsin u)
  have huSq := coarseAngleArgument_sq v
  change u^2 = _ at huSq
  unfold coarseAnglePhi
  rw [Real.cos_two_mul]
  rw [hsin] at htrig
  change 2-2*(2*Real.cos (Real.arcsin u)^2-1) = _
  nlinarith [htrig,huSq]

theorem coarseAnglePhi_profile
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    coarseInverseRadius (2*Real.cos (coarseAnglePhi v)) =
      2*Real.cos v := by
  obtain ⟨he0,heδ⟩ := coarseAngleDeficit_range hv0 hvβ
  have hPhi := coarseAnglePhi_deficit hv0 hvβ
  have harg : 2*Real.cos (coarseAnglePhi v) =
      2-(coarseAngleDeficit v+5*coarseAngleDeficit v^2) := by
    linarith
  rw [harg, coarseInverseRadius_on_projection_loss he0 heδ]
  unfold coarseAngleDeficit
  ring

theorem coarseAnglePhi_beta :
    coarseAnglePhi coarseAngleBeta = coarseAngleAlpha := by
  have hβ0 := coarseAngleBeta_range.1
  have hφrange := coarseAnglePhi_range hβ0 (le_refl coarseAngleBeta)
  have hdef := coarseAnglePhi_deficit hβ0 (le_refl coarseAngleBeta)
  have heβ : coarseAngleDeficit coarseAngleBeta = 1/20 := by
    unfold coarseAngleDeficit coarseAngleBeta
    rw [Real.cos_arccos (by norm_num) (by norm_num)]
    norm_num
  rw [heβ] at hdef
  have hcos : Real.cos (coarseAnglePhi coarseAngleBeta) = 31/32 := by
    norm_num at hdef ⊢
    linarith
  unfold coarseAngleAlpha
  exact (Real.arccos_eq_of_eq_cos hφrange.1 hφrange.2 hcos.symm).symm

theorem coarseAnglePhi_continuous : Continuous coarseAnglePhi := by
  unfold coarseAnglePhi coarseAngleArgument coarseAngleDeficit
  fun_prop

theorem coarseAnglePhi_ge_input
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    v ≤ coarseAnglePhi v := by
  have hvπ : v ≤ Real.pi :=
    hvβ.trans (by linarith [coarseAngleBeta_range.2, Real.pi_pos])
  obtain ⟨hφ0,hφπ⟩ := coarseAnglePhi_range hv0 hvβ
  obtain ⟨he0,_⟩ := coarseAngleDeficit_range hv0 hvβ
  have hcos : Real.cos (coarseAnglePhi v) ≤ Real.cos v := by
    have h := coarseAnglePhi_deficit hv0 hvβ
    unfold coarseAngleDeficit at h
    nlinarith [sq_nonneg (2-2*Real.cos v)]
  have harccos := Real.arccos_le_arccos hcos
  rw [Real.arccos_cos hv0 hvπ, Real.arccos_cos hφ0 hφπ] at harccos
  exact harccos

theorem coarseAnglePhi_le_pi_half
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    coarseAnglePhi v ≤ Real.pi/2 := by
  obtain ⟨he0,heδ⟩ := coarseAngleDeficit_range hv0 hvβ
  obtain ⟨_,hsδ⟩ := coarseProjectionLoss_range he0 heδ
  obtain ⟨hφ0,hφπ⟩ := coarseAnglePhi_range hv0 hvβ
  have hcos : 0 ≤ Real.cos (coarseAnglePhi v) := by
    have h := coarseAnglePhi_deficit hv0 hvβ
    linarith
  have harccos := Real.arccos_le_arccos hcos
  rw [Real.arccos_cos hφ0 hφπ] at harccos
  simpa using harccos

end SpringerLean

#print axioms SpringerLean.coarseAnglePhi_deficit
#print axioms SpringerLean.coarseAnglePhi_profile
#print axioms SpringerLean.coarseAnglePhi_beta
#print axioms SpringerLean.coarseAnglePhi_ge_input
#print axioms SpringerLean.coarseAnglePhi_le_pi_half
