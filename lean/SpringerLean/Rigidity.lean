import SpringerLean.DiskExpansion

open scoped Topology

namespace SpringerLean

private theorem inv_mem_exteriorDisk_of_norm_lt_one
    {u : ℂ} (hu0 : u ≠ 0) (hu : ‖u‖ < 1) :
    u⁻¹ ∈ exteriorDisk := by
  change 1 < ‖u⁻¹‖
  rw [norm_inv]
  have hp : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have h := one_div_lt_one_div_of_lt hp hu
  simpa only [one_div, inv_one] using h

/-- Vanishing of every higher coefficient identifies the actual forward germ
throughout the unit disk. -/
theorem exteriorForwardGerm_eq_linear_on_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hhigh : ∀ j : ℕ, 2 ≤ j → exteriorForwardCoeff F j = 0)
    {u : ℂ} (hu : ‖u‖ < 1) :
    exteriorForwardGerm F u = exteriorForwardCoeff F 1 * u := by
  have hs := exteriorForwardGerm_hasSum_coeff_unitBall F hc hu
  have hterm (j : ℕ) :
      exteriorForwardCoeff F j * u ^ j =
        if j = 1 then exteriorForwardCoeff F 1 * u else 0 := by
    by_cases hj1 : j = 1
    · subst j
      simp
    · by_cases hj0 : j = 0
      · subst j
        simp [exteriorForwardCoeff_zero]
      · have hj2 : 2 ≤ j := by omega
        simp [hj1, hhigh j hj2]
  have hs' : HasSum
      (fun j : ℕ => if j = 1 then exteriorForwardCoeff F 1 * u else 0)
      (exteriorForwardGerm F u) := by
    simpa only [hterm] using hs
  have hsingle : HasSum
      (fun j : ℕ => if j = 1 then exteriorForwardCoeff F 1 * u else 0)
      (exteriorForwardCoeff F 1 * u) := by
    apply hasSum_single (α := ℂ) 1
    intro j hj
    simp [hj]
  exact hs'.unique hsingle

/-- The corresponding slit identity holds on the original exterior domain. -/
theorem exterior_eq_slitMap_on_of_high_coeff_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hhigh : ∀ j : ℕ, 2 ≤ j → exteriorForwardCoeff F j = 0) :
    Set.EqOn F (slitMap (exteriorForwardCoeff F 1)) exteriorDisk := by
  intro z hz
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  have hzlarge : 1 < ‖z‖ := hz
  have hsmall : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hzlarge
    simpa only [one_div, inv_one] using h
  have hlinear := exteriorForwardGerm_eq_linear_on_unitBall F hc hhigh hsmall
  rw [exteriorForwardGerm_punctured F (inv_ne_zero hz0)] at hlinear
  simpa [slitMap, div_eq_mul_inv, add_comm] using (sub_eq_iff_eq_add.mp hlinear)

/-- Forward coefficients depend only on the actual map on the exterior disk. -/
theorem exteriorForwardCoeff_eq_of_eqOn_exterior
    (F G : ℂ → ℂ) (hFG : Set.EqOn F G exteriorDisk)
    (n : ℕ) :
    exteriorForwardCoeff F n = exteriorForwardCoeff G n := by
  have hnear :
      exteriorForwardGerm F =ᶠ[𝓝 (0 : ℂ)] exteriorForwardGerm G := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)]
      with u hu
    by_cases hu0 : u = 0
    · subst u
      simp [exteriorForwardGerm]
    · have hsmall : ‖u‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hu
      have hext := inv_mem_exteriorDisk_of_norm_lt_one hu0 hsmall
      rw [exteriorForwardGerm_punctured F hu0,
        exteriorForwardGerm_punctured G hu0,
        hFG hext]
  simpa only [exteriorForwardCoeff, actualTaylorCoeff] using
    (actualTaylorCoeff_congr hnear n)

/-- The first positive Laurent coefficient of a slit map is its parameter. -/
theorem exteriorForwardCoeff_slitMap_one (a : ℂ) :
    exteriorForwardCoeff (slitMap a) 1 = a := by
  have hfun : exteriorForwardGerm (slitMap a) =
      (fun u : ℂ => a * u) := by
    funext u
    by_cases hu : u = 0
    · simp [exteriorForwardGerm, hu]
    · simp [exteriorForwardGerm, slitMap, hu, div_eq_mul_inv]
  simp [exteriorForwardCoeff, hfun, iteratedDeriv_succ']

/-- Equality classification with the finite area estimate as an explicit
premise. `GeneralArea.lean` discharges it for the paper's original class. -/
theorem exteriorInverseCoeff_one_norm_eq_one_iff_slit_of_finite_area
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (harea : ∀ N : ℕ,
      (∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤ 1) :
    ‖exteriorInverseCoeff F 1‖ = 1 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  constructor
  · intro hB
    have hfirst : ‖exteriorForwardCoeff F 1‖ = 1 := by
      simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hB
    have hhigh := exteriorForwardCoeff_eq_zero_of_finite_area_equality
      F harea hfirst
    exact ⟨exteriorForwardCoeff F 1, hfirst,
      exterior_eq_slitMap_on_of_high_coeff_zero F hc hhigh⟩
  · rintro ⟨a, ha, hFG⟩
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
      exteriorForwardCoeff_eq_of_eqOn_exterior F (slitMap a) hFG 1,
      exteriorForwardCoeff_slitMap_one]
    exact ha

end SpringerLean
