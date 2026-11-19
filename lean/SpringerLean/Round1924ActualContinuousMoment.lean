import SpringerLean.Round1923ActualFourToEight
import SpringerLean.Round1870SlitMomentRotation

namespace SpringerLean

theorem slitRadialMomentConstant_pos
    {p : ℝ} (hp : 0 < p) : 0 < slitRadialMomentConstant p := by
  unfold slitRadialMomentConstant
  apply div_pos (Real.Gamma_pos_of_pos (by linarith))
  exact sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith))

/-- Quantitative boundary-moment theorem for every real p in [4,8], on
the original actual radial trace. -/
theorem actualBoundaryRadialMoment_four_to_eight_margin
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {p : ℝ} (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    actualBoundaryRadialMoment F p ≤
      slitRadialMomentConstant p *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80) := by
  have h := normalized_actual_radial_moment_four_to_eight F hc hp4 hp8
  rw [normalizedActualRadialMoment,
    normalizedCosineMoment_eq_slit_constant p (by linarith)] at h
  have hpow : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hdiv : actualBoundaryRadialMoment F p / (2 : ℝ) ^ p ≤
      (slitRadialMomentConstant p *
        (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80)) /
          (2 : ℝ) ^ p := by
    convert h using 1
    ring
  exact (div_le_div_iff_of_pos_right hpow).mp hdiv

theorem actualBoundaryRadialMoment_four_to_eight_eq_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {p : ℝ} (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    actualBoundaryRadialMoment F p = slitRadialMomentConstant p ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  constructor
  · intro heq
    have hbound := actualBoundaryRadialMoment_four_to_eight_margin F hc hp4 hp8
    rw [heq] at hbound
    have hS := slitRadialMomentConstant_pos (by linarith : 0 < p)
    have hx : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
      have hh := exteriorInverseCoeff_one_norm_le F hc
      rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at hh
      exact hh
    have hx0 : 0 ≤ ‖exteriorForwardCoeff F 1‖ := norm_nonneg _
    have hx1 : ‖exteriorForwardCoeff F 1‖ = 1 := by
      have hDle : 1 - ‖exteriorForwardCoeff F 1‖ ^ 2 ≤ 0 := by
        by_contra hh
        have hDpos : 0 < 1 - ‖exteriorForwardCoeff F 1‖ ^ 2 :=
          lt_of_not_ge hh
        have hmul := mul_pos hS hDpos
        nlinarith
      nlinarith
    apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit F hc).mp
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
    exact hx1
  · rintro ⟨a, ha, hEq⟩
    exact actualBoundaryRadialMoment_eq_of_eqOn_slit F hc a ha hEq p
      (by linarith)

end SpringerLean

namespace SpringerLean.PaperStatementsAudit

/-- Continuous real-exponent statement with the exact original function
class, actual radial trace, quantitative margin, and slit iff. -/
theorem theorem_9_1_p4_to_p8_actual_radial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {p : ℝ} (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    actualBoundaryRadialMoment F p ≤
        slitRadialMomentConstant p *
          (1 - (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80) ∧
      (actualBoundaryRadialMoment F p = slitRadialMomentConstant p ↔
        ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  exact ⟨actualBoundaryRadialMoment_four_to_eight_margin F hc hp4 hp8,
    actualBoundaryRadialMoment_four_to_eight_eq_iff_slit F hc hp4 hp8⟩

end SpringerLean.PaperStatementsAudit

#check @SpringerLean.PaperStatementsAudit.theorem_9_1_p4_to_p8_actual_radial
#print axioms SpringerLean.PaperStatementsAudit.theorem_9_1_p4_to_p8_actual_radial
