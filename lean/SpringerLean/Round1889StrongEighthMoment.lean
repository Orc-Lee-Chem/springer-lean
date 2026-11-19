import SpringerLean.Round1883ActualEighthMomentSlit

open Filter
open scoped Topology

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- The squared W-block bound, retaining the quadratic area remainder. -/
theorem eighth_w_actual_strong_energy_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    8 * ‖exteriorForwardCoeff F 5 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
      exteriorForwardCoeff F 1 ^ 3‖ ^ 2 ≤
      8 + (56 / 9 - (8 / 9) * ‖exteriorForwardCoeff F 1‖ ^ 2) *
        (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let D := 1 - ‖exteriorForwardCoeff F 1‖ ^ 2
  let w := exteriorForwardCoeff F 5 +
    3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
    (3 / 2 : ℂ) * exteriorForwardCoeff F 2 ^ 2 +
    exteriorForwardCoeff F 1 ^ 3
  have hD0 : 0 ≤ D := by
    have h := exteriorInverseCoeff_one_norm_le F hc
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at h
    dsimp only [D]
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  have hw : ‖w‖ ≤ 1 + D / 3 := eighth_w_actual_bound F hc
  have hwsq : ‖w‖ ^ 2 ≤ (1 + D / 3) ^ 2 := by
    nlinarith [norm_nonneg w]
  dsimp only [D, w] at *
  nlinarith

/-- Direct expansion of the residual polynomial from the actual p=8 blocks. -/
theorem eighth_strong_residual_factor (s : ℝ) :
    (48 + 24 * s - (144 / 5) * s - 56 / 9 - 2 / 3 -
      9 * s - (9 / 2) * (1 + s) ^ 2 + 8 * s / 9) - 51 / 5 =
      (1 - s) * (405 * s + 2377) / 90 := by
  ring

theorem eighth_strong_scalar_margin {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    2 + 24 * s +
      (12 + 24 * s ^ 2 + (144 / 5) * s * (1 - s)) +
      (8 + (56 / 9 - 8 * s / 9) * (1 - s)) +
      (2 / 3 + 9 * s + (9 / 2) * (1 + s) ^ 2) * (1 - s) ≤
      70 - (51 / 5) * (1 - s) := by
  have hD : 0 ≤ 1 - s := by linarith
  have hpoly : 0 ≤ 405 * s + 2377 := by linarith
  have hfactor := eighth_strong_residual_factor s
  have hP : (51 / 5 : ℝ) ≤
      48 + 24 * s - (144 / 5) * s - 56 / 9 - 2 / 3 -
        9 * s - (9 / 2) * (1 + s) ^ 2 + 8 * s / 9 := by
    nlinarith [mul_nonneg hD hpoly]
  have hmul := mul_le_mul_of_nonneg_right hP hD
  nlinarith

theorem rescaleExterior_boundary_eight_strong_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖rescaleExterior r F z‖ ^ 8) 0 1 ≤
      70 - (51 / 5) *
        (1 - ‖exteriorForwardCoeff (rescaleExterior r F) 1‖ ^ 2) := by
  let G := rescaleExterior r F
  have hG : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hr0 hr1
  let s : ℝ := ‖exteriorForwardCoeff G 1‖ ^ 2
  have hs0 : 0 ≤ s := sq_nonneg _
  have hs1 : s ≤ 1 := by
    have hb := exteriorInverseCoeff_one_norm_le G hG
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one G hG] at hb
    dsimp only [s]
    nlinarith [norm_nonneg (exteriorForwardCoeff G 1)]
  have hfirst := eighth_first_block_budget G hG
  have hw := eighth_w_actual_strong_energy_bound G hG
  have hy := eighth_y_actual_energy_bound G hG
  have hfinite := rescaleExterior_boundary_eight_le_coeff F hc hr0 hr1
  have hscalar := eighth_strong_scalar_margin hs0 hs1
  dsimp only [s, G] at hscalar
  dsimp only [G] at hfirst hw hy
  nlinarith

theorem actualBoundaryRadialMoment_eight_strong_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 8 ≤
      70 - (51 / 5) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  have hleft : Tendsto
      (fun s : ℝ => Real.circleAverage
        (fun z : ℂ => ‖rescaleExterior s F z‖ ^ 8) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 8)) := by
    simpa only [Real.rpow_ofNat] using
      actualBoundaryRadialMoment_rescale_circle_tendsto F hc 8 (by norm_num)
  have hright : Tendsto
      (fun s : ℝ => 70 - (51 / 5) *
        (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2))
      (𝓝[<] (1 : ℝ))
      (𝓝 (70 - (51 / 5) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2))) := by
    have hcont : Continuous
        (fun s : ℝ => 70 - (51 / 5) *
          (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2)) := by
      fun_prop
    simpa only [Complex.ofReal_one, one_pow, one_mul] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hh := rescaleExterior_boundary_eight_strong_margin F hc hs.1 hs.2
  rw [rescaleExterior_forwardCoeff F hc hs.1] at hh
  simpa only [Nat.reduceAdd] using hh

end SpringerLean

namespace SpringerLean.PaperStatementsAudit

/-- Revised eighth-moment bound on the actual radial trace, with the complete
fixed-order equality classification. -/
theorem theorem_9_1_p8_actual_radial_strong
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 8 ≤
        70 - (51 / 5) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) ∧
      (actualBoundaryRadialMoment F 8 = slitRadialMomentConstant 8 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  refine ⟨actualBoundaryRadialMoment_eight_strong_margin F hc, ?_⟩
  exact (theorem_9_1_p8_actual_radial F hc).2

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial_strong
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial_strong
