import SpringerLean.Round13Mean

namespace SpringerLean

/-- The holomorphic factor used to study logarithmic boundary potentials
for the actual regularized exterior map. -/
noncomputable def regularBoundaryPotential (s : ℝ)
    (F : ℂ → ℂ) (w u : ℂ) : ℂ :=
  1 - w * u + u * regularForwardGerm s F u

@[simp] theorem regularBoundaryPotential_zero
    (s : ℝ) (F : ℂ → ℂ) (w : ℂ) :
    regularBoundaryPotential s F w 0 = 1 := by
  simp [regularBoundaryPotential]

theorem regularBoundaryPotential_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) (w : ℂ) :
    AnalyticOnNhd ℂ (regularBoundaryPotential s F w)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hG := regularForwardGerm_analyticOnNhd F hc hs u hu
  change AnalyticAt ℂ
    (fun v : ℂ => 1 - w * v + v * regularForwardGerm s F v) u
  fun_prop

/-- Off zero, the factor is the actual exterior-map difference multiplied
by the reciprocal coordinate. -/
theorem regularBoundaryPotential_punctured
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s)
    (w : ℂ) {u : ℂ} (hu : u ≠ 0) :
    regularBoundaryPotential s F w u =
      u * (rescaleExterior s F u⁻¹ - w) := by
  rw [regularBoundaryPotential, regularForwardGerm_eq_actual s hs F,
    exteriorForwardGerm_punctured _ hu]
  field_simp [hu]
  ring

private theorem reciprocal_mem_exteriorDisk_of_norm_lt_one
    {u : ℂ} (hu0 : u ≠ 0) (hu : ‖u‖ < 1) :
    u⁻¹ ∈ exteriorDisk := by
  change 1 < ‖u⁻¹‖
  rw [norm_inv]
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have h := one_div_lt_one_div_of_lt hpos hu
  simpa only [one_div, inv_one] using h

/-- If `w` is in the actual omitted set of the regularized exterior map,
the potential factor has no zeros anywhere in the open unit disk. -/
theorem regularBoundaryPotential_ne_zero_of_omitted
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s)
    {w : ℂ} (hw : w ∈ exteriorOmitted (rescaleExterior s F))
    {u : ℂ} (hu : ‖u‖ < 1) :
    regularBoundaryPotential s F w u ≠ 0 := by
  intro hq
  have hu0 : u ≠ 0 := by
    intro hzero
    subst u
    simp at hq
  have hext := reciprocal_mem_exteriorDisk_of_norm_lt_one hu0 hu
  have hwImage : w ∈ rescaleExterior s F '' exteriorDisk := by
    refine ⟨u⁻¹, hext, ?_⟩
    have h := regularBoundaryPotential_punctured F hs w hu0
    rw [h] at hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hu0)
  exact hw hwImage

/-- Every actual exterior preimage gives a disk zero at its reciprocal. -/
theorem regularBoundaryPotential_zero_of_image
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    regularBoundaryPotential s F (rescaleExterior s F v) v⁻¹ = 0 := by
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num [exteriorDisk] at hv
  rw [regularBoundaryPotential_punctured F hs _ (inv_ne_zero hv0), inv_inv,
    sub_self, mul_zero]

/-- For a value in the actual regularized exterior image, the reciprocal
of its unique exterior preimage is the unique zero in the open unit disk. -/
theorem regularBoundaryPotential_zero_unique_of_image
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk)
    {u : ℂ} (hu : ‖u‖ < 1)
    (hq : regularBoundaryPotential s F (rescaleExterior s F v) u = 0) :
    u = v⁻¹ := by
  have hu0 : u ≠ 0 := by
    intro hzero
    subst u
    simp at hq
  have hext := reciprocal_mem_exteriorDisk_of_norm_lt_one hu0 hu
  have himage : rescaleExterior s F u⁻¹ = rescaleExterior s F v := by
    rw [regularBoundaryPotential_punctured F hs0 _ hu0] at hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hu0)
  have hinj := (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1).2.1
  have heq : u⁻¹ = v := hinj hext hv himage
  calc
    u = (u⁻¹)⁻¹ := by simp
    _ = v⁻¹ := congrArg Inv.inv heq

end SpringerLean
