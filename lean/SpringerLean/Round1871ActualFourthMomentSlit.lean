import SpringerLean.Round1868ActualFourthMoment
import SpringerLean.Round1870SlitMomentRotation

namespace SpringerLean

/-- A second complete certificate-free real-exponent instance of the
radial theorem, with the stronger 1/2 deficit and full slit iff. -/
theorem actualBoundaryRadialMoment_four_margin_and_eq_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 4 ≤ slitRadialMomentConstant 4 *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 2) ∧
      (actualBoundaryRadialMoment F 4 = slitRadialMomentConstant 4 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  refine ⟨actualBoundaryRadialMoment_four_quantitative F hc, ?_⟩
  constructor
  · exact actualBoundaryRadialMoment_four_eq_imp_slit F hc
  · rintro ⟨a, ha, hEq⟩
    exact actualBoundaryRadialMoment_eq_of_eqOn_slit F hc a ha hEq 4 (by norm_num)

end SpringerLean

namespace SpringerLean.PaperStatementsAudit

theorem theorem_9_1_p4_actual_radial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 4 ≤ slitRadialMomentConstant 4 *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 2) ∧
      (actualBoundaryRadialMoment F 4 = slitRadialMomentConstant 4 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :=
  actualBoundaryRadialMoment_four_margin_and_eq_iff_slit F hc

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p4_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p4_actual_radial
