import SpringerLean.Round2026DiskSchwarzRigidity

namespace SpringerLean

/-- The actual disk transition obtained by applying the chosen exterior
inverse of G to the actual value of F, then reciprocating. -/
noncomputable def exteriorTransitionDisk (F G : ℂ → ℂ) (t : ℂ) : ℂ :=
  if t = 0 then 0 else (exteriorInverse G (F t⁻¹))⁻¹

theorem exteriorTransitionDisk_zero (F G : ℂ → ℂ) :
    exteriorTransitionDisk F G 0 = 0 := by
  simp [exteriorTransitionDisk]

theorem exteriorTransitionDisk_mem_ball
    (F G : ℂ → ℂ)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) :
    exteriorTransitionDisk F G t ∈ Metric.ball (0:ℂ) 1 := by
  by_cases ht0 : t = 0
  · subst t
    simp [exteriorTransitionDisk]
  · have htnorm : ‖t‖ < 1 := by simpa using ht
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have htinv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt htpos htnorm
      simpa [one_div] using h
    have hFimage : F t⁻¹ ∈ G '' exteriorDisk := by
      rw [← hImage]
      exact ⟨t⁻¹, htinv, rfl⟩
    have hGinv : exteriorInverse G (F t⁻¹) ∈ exteriorDisk := by
      exact Function.invFunOn_mem hFimage
    have hInvNorm : ‖(exteriorInverse G (F t⁻¹))⁻¹‖ < 1 := by
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) hGinv
      simpa [one_div] using h
    simpa [exteriorTransitionDisk, ht0] using hInvNorm

theorem exteriorTransitionDisk_functional
    (F G : ℂ → ℂ)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) (ht0 : t ≠ 0) :
    G ((exteriorTransitionDisk F G t)⁻¹) = F t⁻¹ := by
  have htnorm : ‖t‖ < 1 := by simpa using ht
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have htinv : t⁻¹ ∈ exteriorDisk := by
    change 1 < ‖t⁻¹‖
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt htpos htnorm
    simpa [one_div] using h
  have hFimage : F t⁻¹ ∈ G '' exteriorDisk := by
    rw [← hImage]
    exact ⟨t⁻¹, htinv, rfl⟩
  simp [exteriorTransitionDisk, ht0, exteriorInverse,
    Function.invFunOn_eq hFimage]

theorem exteriorTransitionDisk_ne_zero
    (F G : ℂ → ℂ)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) (ht0 : t ≠ 0) :
    exteriorTransitionDisk F G t ≠ 0 := by
  have htnorm : ‖t‖ < 1 := by simpa using ht
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have htinv : t⁻¹ ∈ exteriorDisk := by
    change 1 < ‖t⁻¹‖
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt htpos htnorm
    simpa [one_div] using h
  have hFimage : F t⁻¹ ∈ G '' exteriorDisk := by
    rw [← hImage]
    exact ⟨t⁻¹, htinv, rfl⟩
  have hGinv : exteriorInverse G (F t⁻¹) ∈ exteriorDisk :=
    Function.invFunOn_mem hFimage
  have hGinv0 : exteriorInverse G (F t⁻¹) ≠ 0 := by
    intro hzero
    simp [hzero, exteriorDisk] at hGinv
    norm_num at hGinv
  simp [exteriorTransitionDisk, ht0, hGinv0]

theorem exteriorTransitionDisk_inverse
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) :
    exteriorTransitionDisk G F (exteriorTransitionDisk F G t) = t := by
  by_cases ht0 : t = 0
  · simp [ht0, exteriorTransitionDisk]
  · let s := exteriorTransitionDisk F G t
    have hs : s ∈ Metric.ball (0:ℂ) 1 :=
      exteriorTransitionDisk_mem_ball F G hImage t ht
    have hs0 : s ≠ 0 := exteriorTransitionDisk_ne_zero F G hImage t ht ht0
    have hEq : G s⁻¹ = F t⁻¹ :=
      exteriorTransitionDisk_functional F G hImage t ht ht0
    have htnorm : ‖t‖ < 1 := by simpa using ht
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have htinv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt htpos htnorm
      simpa [one_div] using h
    have hFinv : exteriorInverse F (G s⁻¹) = t⁻¹ := by
      rw [hEq]
      exact hF.2.1.leftInvOn_invFunOn htinv
    change exteriorTransitionDisk G F s = t
    simp [exteriorTransitionDisk, hs0, hFinv]

end SpringerLean

#print axioms SpringerLean.exteriorTransitionDisk_mem_ball
#print axioms SpringerLean.exteriorTransitionDisk_functional
#print axioms SpringerLean.exteriorTransitionDisk_inverse
