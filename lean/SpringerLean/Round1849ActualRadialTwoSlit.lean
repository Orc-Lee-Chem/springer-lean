import SpringerLean.Round1848ActualBoundaryParseval
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open scoped Topology

namespace SpringerLean

/-- The gamma normalization used for boundary radial moments. -/
noncomputable def slitRadialMomentConstant (p : ℝ) : ℝ :=
  Real.Gamma (p + 1) / Real.Gamma (1 + p / 2) ^ 2

theorem slitRadialMomentConstant_two : slitRadialMomentConstant 2 = 2 := by
  have h2 : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have h3 : Real.Gamma 3 = 2 := by
    simpa using Real.Gamma_nat_eq_factorial 2
  norm_num [slitRadialMomentConstant, h2, h3]

/-- Full slit equality classification for the actual a.e. radial second
moment.  Both directions concern EqOn on the open exterior disk. -/
theorem actualBoundaryRadialMoment_two_eq_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 2 = 2 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  constructor
  · intro h
    apply exteriorForwardCoeff_tsum_radial_two_eq_slit F hc
    rwa [← actualBoundaryRadialMoment_two_eq_coeff F hc]
  · intro h
    have hb := (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).2 h
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at hb
    have hlo := (exteriorForwardCoeff_sq_summable F hc).le_tsum 1
      (fun j _ => sq_nonneg (‖exteriorForwardCoeff F j‖))
    have hhi := actualBoundaryRadialMoment_two_margin F hc
    rw [hb] at hlo hhi
    rw [actualBoundaryRadialMoment_two_eq_coeff F hc] at hhi ⊢
    nlinarith

/-- Original-hypothesis p=2 instance, with the stronger 1/4 margin and
the actual trace.  The full real-exponent interval is a separate target. -/
theorem actualBoundaryRadialMoment_two_margin_and_eq_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 2 ≤
        slitRadialMomentConstant 2 *
          (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) ∧
      (actualBoundaryRadialMoment F 2 = slitRadialMomentConstant 2 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  rw [slitRadialMomentConstant_two]
  exact ⟨actualBoundaryRadialMoment_two_margin F hc,
    actualBoundaryRadialMoment_two_eq_iff_slit F hc⟩

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_two_eq_iff_slit
#print axioms SpringerLean.actualBoundaryRadialMoment_two_margin_and_eq_iff_slit
