import SpringerLean.Round1849ActualRadialTwoSlit

namespace SpringerLean.PaperStatementsAudit

/-- The actual boundary p=2 instance of original Theorem 9.1.  Its 1/4
margin is stronger than the original 1/1000 margin at p=2. -/
theorem theorem_9_1_p2_actual_radial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 2 ≤
        slitRadialMomentConstant 2 *
          (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 4) ∧
      (actualBoundaryRadialMoment F 2 = slitRadialMomentConstant 2 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :=
  actualBoundaryRadialMoment_two_margin_and_eq_iff_slit F hc

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p2_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p2_actual_radial
