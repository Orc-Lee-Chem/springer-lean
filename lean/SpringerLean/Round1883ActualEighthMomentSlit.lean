import SpringerLean.Round1882ActualEighthMoment
import SpringerLean.Round1870SlitMomentRotation

namespace SpringerLean.PaperStatementsAudit

/-- The complete eighth-moment instance on the actual exterior map,
with the explicit deficit and full fixed-order slit classification. -/
theorem theorem_9_1_p8_actual_radial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 8 ≤ slitRadialMomentConstant 8 *
        (1 - (9 / 70) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)) ∧
      (actualBoundaryRadialMoment F 8 = slitRadialMomentConstant 8 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  refine ⟨actualBoundaryRadialMoment_eight_quantitative F hc, ?_⟩
  constructor
  · exact actualBoundaryRadialMoment_eight_eq_imp_slit F hc
  · rintro ⟨a, ha, hEq⟩
    exact actualBoundaryRadialMoment_eq_of_eqOn_slit F hc a ha hEq 8 (by norm_num)

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p8_actual_radial
