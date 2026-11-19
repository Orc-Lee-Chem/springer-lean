import SpringerLean.Round1866FourthMomentFiniteEnergy
import SpringerLean.Round1867ActualRescaledMomentLimit

open Filter
open scoped Topology

namespace SpringerLean

theorem rescaleExterior_boundary_four_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 4) 0 1 ≤
      6 - 3 * (1 - ‖exteriorForwardCoeff (rescaleExterior s F) 1‖ ^ 2) := by
  have hfinite := rescaleExterior_boundary_four_le_coeff F hc hs0 hs1
  have harea := exteriorForwardCoeff_finite_area (rescaleExterior s F)
    (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1) 2
  have hset : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hset] at harea
  norm_num at harea
  linarith

/-- A second certificate-free quantitative instance, obtained by the
actual weighted area formula and the full radial limit. -/
theorem actualBoundaryRadialMoment_four_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 4 ≤
      6 - 3 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  have hleft : Tendsto
      (fun s : ℝ => Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 4) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F 4)) := by
    simpa only [Real.rpow_ofNat] using
      actualBoundaryRadialMoment_rescale_circle_tendsto F hc 4 (by norm_num)
  have hright : Tendsto
      (fun s : ℝ => 6 - 3 * (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2))
      (𝓝[<] (1 : ℝ)) (𝓝 (6 - 3 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2))) := by
    have hcont : Continuous
        (fun s : ℝ => 6 - 3 * (1 - ‖(s : ℂ) ^ 2 * exteriorForwardCoeff F 1‖ ^ 2)) := by
      fun_prop
    simpa only [Complex.ofReal_one, one_pow, one_mul] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  have hh := rescaleExterior_boundary_four_margin F hc hs.1 hs.2
  rw [rescaleExterior_forwardCoeff F hc hs.1] at hh
  simpa only [Nat.reduceAdd] using hh

theorem slitRadialMomentConstant_four : slitRadialMomentConstant 4 = 6 := by
  have h3 : Real.Gamma 3 = 2 := by simpa using Real.Gamma_nat_eq_factorial 2
  have h5 : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1 <;> norm_num
  norm_num [slitRadialMomentConstant, h3, h5]

theorem actualBoundaryRadialMoment_four_quantitative
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 4 ≤ slitRadialMomentConstant 4 *
      (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 2) := by
  rw [slitRadialMomentConstant_four]
  convert actualBoundaryRadialMoment_four_margin F hc using 1 <;> ring

theorem actualBoundaryRadialMoment_four_eq_imp_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (heq : actualBoundaryRadialMoment F 4 = slitRadialMomentConstant 4) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  have hmargin := actualBoundaryRadialMoment_four_margin F hc
  have hβle : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
      exteriorInverseCoeff_one_norm_le F hc
  rw [slitRadialMomentConstant_four] at heq
  have hβ : ‖exteriorForwardCoeff F 1‖ = 1 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).1
  simpa only [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using hβ

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_four_quantitative
#print axioms SpringerLean.actualBoundaryRadialMoment_four_eq_imp_slit
