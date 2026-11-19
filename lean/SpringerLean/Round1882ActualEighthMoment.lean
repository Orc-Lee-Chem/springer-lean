import SpringerLean.Round1881EighthYBlock
import SpringerLean.Round1867ActualRescaledMomentLimit

open Filter
open scoped Topology

namespace SpringerLean

set_option maxHeartbeats 2000000

/-- The elementary concave residual from the three p=8 coefficient
blocks is uniformly larger than nine on the full area range. -/
theorem eighth_scalar_margin {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    2 + 24 * s +
      (12 + 24 * s ^ 2 + (144 / 5) * s * (1 - s)) +
      (8 + (56 / 9) * (1 - s)) +
      (2 / 3 + 9 * s + (9 / 2) * (1 + s) ^ 2) * (1 - s) ≤
      70 - 9 * (1 - s) := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have hP : (9 : ℝ) ≤
      48 + 24 * s - (144 / 5) * s - 56 / 9 - 2 / 3 -
        9 * s - (9 / 2) * (1 + s) ^ 2 := by
    nlinarith
  have hD : 0 ≤ 1 - s := by linarith
  have hmul := mul_le_mul_of_nonneg_right hP hD
  nlinarith

theorem rescaleExterior_boundary_eight_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior r F ζ‖ ^ 8) 0 1 ≤
      70 - 9 * (1 - ‖exteriorForwardCoeff (rescaleExterior r F) 1‖ ^ 2) := by
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
  have hw := eighth_w_actual_energy_bound G hG
  have hy := eighth_y_actual_energy_bound G hG
  have hfinite := rescaleExterior_boundary_eight_le_coeff F hc hr0 hr1
  have hscalar := eighth_scalar_margin hs0 hs1
  dsimp only [s, G] at hscalar
  dsimp only [G] at hfirst hw hy
  nlinarith

theorem actualBoundaryRadialMoment_eight_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 8 ≤
      70 - 9 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  have hleft : Tendsto
      (fun s : ℝ => Real.circleAverage
        (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 8) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 8)) := by
    simpa only [Real.rpow_ofNat] using
      actualBoundaryRadialMoment_rescale_circle_tendsto F hc 8 (by norm_num)
  have hright : Tendsto
      (fun s : ℝ => 70 - 9 *
        (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2))
      (𝓝[<] (1 : ℝ))
      (𝓝 (70 - 9 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2))) := by
    have hcont : Continuous
        (fun s : ℝ => 70 - 9 *
          (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2)) := by
      fun_prop
    simpa only [Complex.ofReal_one, one_pow, one_mul] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hh := rescaleExterior_boundary_eight_margin F hc hs.1 hs.2
  rw [rescaleExterior_forwardCoeff F hc hs.1] at hh
  simpa only [Nat.reduceAdd] using hh

theorem slitRadialMomentConstant_eight : slitRadialMomentConstant 8 = 70 := by
  have h5 : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1 <;> norm_num
  have h9 : Real.Gamma 9 = 40320 := by
    convert Real.Gamma_nat_eq_factorial 8 using 1 <;> norm_num
  norm_num [slitRadialMomentConstant, h5, h9]

theorem actualBoundaryRadialMoment_eight_quantitative
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 8 ≤ slitRadialMomentConstant 8 *
      (1 - (9 / 70) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)) := by
  rw [slitRadialMomentConstant_eight]
  convert actualBoundaryRadialMoment_eight_margin F hc using 1 <;> ring

theorem actualBoundaryRadialMoment_eight_eq_imp_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (heq : actualBoundaryRadialMoment F 8 = slitRadialMomentConstant 8) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  have hmargin := actualBoundaryRadialMoment_eight_margin F hc
  have hble : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
      exteriorInverseCoeff_one_norm_le F hc
  rw [slitRadialMomentConstant_eight] at heq
  have hb : ‖exteriorForwardCoeff F 1‖ = 1 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).1
  simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hb

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_eight_quantitative
#print axioms SpringerLean.actualBoundaryRadialMoment_eight_eq_imp_slit
