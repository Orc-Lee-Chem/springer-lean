import SpringerLean.Round1877SixthMomentFiniteEnergy
import SpringerLean.Round1870SlitMomentRotation

namespace SpringerLean.PaperStatementsAudit

/-- The complete sixth-moment instance on the actual exterior map,
with a quantitative deficit and fixed-order slit classification. -/
theorem theorem_9_1_p6_actual_radial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualBoundaryRadialMoment F 6 ≤ slitRadialMomentConstant 6 *
        (1 - (9 / 40) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)) ∧
      (actualBoundaryRadialMoment F 6 = slitRadialMomentConstant 6 ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  refine ⟨actualBoundaryRadialMoment_six_quantitative F hc, ?_⟩
  constructor
  · exact actualBoundaryRadialMoment_six_eq_imp_slit F hc
  · rintro ⟨a, ha, hEq⟩
    exact actualBoundaryRadialMoment_eq_of_eqOn_slit F hc a ha hEq 6 (by norm_num)

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p6_actual_radial
