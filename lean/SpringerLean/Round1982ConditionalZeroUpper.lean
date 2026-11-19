import SpringerLean.Round1974DerivativeZeroMomentNormalization
import SpringerLean.Round1899PolynomialSlitObstruction
import SpringerLean.Round1924ActualContinuousMoment

open Polynomial

namespace SpringerLean

/-- Exact assembly of the 9.2 strict upper once the two remaining
analytic comparisons are supplied. These hypotheses are explicit:
the published derivative-zero radial-power comparison and the
subharmonic zero-to-actual-boundary comparison. This is a reduction,
not the final unrestricted 9.2 theorem. -/
theorem polynomial_derivative_zero_moment_strict_of_analytic_comparisons
    (Q : ℂ[X]) (hQ : Q.Monic) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hidentity : ∀ w ∈ exteriorDisk,
      Q.eval (F w) = w ^ Q.natDegree)
    (j : ℕ) (_hj : j < Q.natDegree)
    (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8)
    (hderivative :
      ((((derivative^[j]) Q).roots.map
        (fun z : ℂ => ‖z‖ ^ p)).sum) /
          ((Q.natDegree - j : ℕ) : ℝ) ≤
      ((Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum) /
          (Q.natDegree : ℝ))
    (hzeroBoundary :
      ((Q.roots.map (fun z : ℂ => ‖z‖ ^ p)).sum) /
          (Q.natDegree : ℝ) ≤ actualBoundaryRadialMoment F p) :
    ((((derivative^[j]) Q).roots.map
      (fun z : ℂ => ‖z‖ ^ p)).sum) /
        ((Q.natDegree - j : ℕ) : ℝ) < slitRadialMomentConstant p := by
  have hnorm : ‖exteriorForwardCoeff F 1‖ ≤ 1 := by
    have h := exteriorInverseCoeff_one_norm_le F hF
    rwa [exteriorInverseCoeff_one_eq_forwardCoeff_one F hF] at h
  have hD : 0 ≤ 1 - ‖exteriorForwardCoeff F 1‖ ^ 2 := by
    nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  have hSpos : 0 < slitRadialMomentConstant p :=
    slitRadialMomentConstant_pos (by linarith)
  have hmargin :=
    actualBoundaryRadialMoment_four_to_eight_margin F hF hp4 hp8
  have hSgap : 0 ≤ slitRadialMomentConstant p *
      ((1 - ‖exteriorForwardCoeff F 1‖ ^ 2) / 80) :=
    mul_nonneg hSpos.le (div_nonneg hD (by norm_num))
  have hRle : actualBoundaryRadialMoment F p ≤
      slitRadialMomentConstant p := by
    nlinarith
  have hRne : actualBoundaryRadialMoment F p ≠
      slitRadialMomentConstant p := by
    intro heq
    obtain ⟨a, ha, hEq⟩ :=
      (actualBoundaryRadialMoment_four_to_eight_eq_iff_slit
        F hF hp4 hp8).mp heq
    have ha0 : a ≠ 0 := by
      intro hzero
      simp [hzero] at ha
    have hslit : ∀ w : ℂ, 1 < ‖w‖ →
        Q.eval (w + a / w) = w ^ Q.natDegree := by
      intro w hw
      have hwext : w ∈ exteriorDisk := hw
      have hFw := hEq hwext
      simpa [slitMap, hFw] using hidentity w hwext
    exact monicPolynomial_no_exterior_slit_identity
      Q hQ Q.natDegree rfl hdeg a ha0 hslit
  have hRlt : actualBoundaryRadialMoment F p <
      slitRadialMomentConstant p := lt_of_le_of_ne hRle hRne
  exact (hderivative.trans hzeroBoundary).trans_lt hRlt

end SpringerLean

#print axioms SpringerLean.polynomial_derivative_zero_moment_strict_of_analytic_comparisons
