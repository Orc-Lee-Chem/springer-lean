import SpringerLean.Round457OmittedSquareRootLift
import SpringerLean.GeneralArea

open scoped Topology

namespace SpringerLean
set_option Elab.async false

theorem omittedSquareRootLift_forwardCoeff_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (P : ℂ)
    (R : ℂ → ℂ) (hRa : AnalyticOnNhd ℂ R (Metric.ball (0 : ℂ) 1))
    (hR0 : R 0 = 1)
    (hRpow : ∀ u ∈ Metric.ball (0 : ℂ) 1,
      R u ^ 2 = exteriorPhi F u - P * u) :
    exteriorForwardCoeff (omittedSquareRootLift R) 1 = -P / 2 := by
  have hR := (hRa 0 (by simp)).differentiableAt.hasDerivAt
  have hPhi : HasDerivAt (exteriorPhi F) 0 0 := by
    convert (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
      ((hasDerivAt_id (0 : ℂ)).mul hc.2.2.differentiableAt.hasDerivAt) using 1
      <;> first | rfl | simp [exteriorPhi, exteriorForwardGerm_zero]
  have hRight : HasDerivAt (fun u : ℂ => exteriorPhi F u - P * u) (-P) 0 := by
    convert hPhi.sub ((hasDerivAt_const (0 : ℂ) P).mul (hasDerivAt_id (0 : ℂ))) using 1
      <;> first | rfl | simp
  have hLeft : HasDerivAt (fun u : ℂ => R u ^ 2) (2 * deriv R 0) 0 := by
    convert hR.pow 2 using 1 <;> first | rfl | simp [hR0]
  have heq : (fun u : ℂ => exteriorPhi F u - P * u) =ᶠ[𝓝 0]
      (fun u => R u ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with u hu
    exact (hRpow u hu).symm
  have hd : 2 * deriv R 0 = -P :=
    (hLeft.congr_of_eventuallyEq heq).unique hRight
  have hds := analyticAt_dslope_zero R (hRa 0 (by simp))
  have hds' : AnalyticAt ℂ (dslope R 0) ((0 : ℂ) ^ 2) := by simpa using hds
  have hComp : AnalyticAt ℂ (fun u : ℂ => dslope R 0 (u ^ 2)) 0 := by
    exact hds'.comp (f := fun u : ℂ => u ^ 2) (x := 0) (analyticAt_id.pow 2)
  have hg : HasDerivAt (fun u : ℂ => u * dslope R 0 (u ^ 2)) (deriv R 0) 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hComp.differentiableAt.hasDerivAt using 1
      <;> first | rfl | simp [dslope_same]
  simp only [exteriorForwardCoeff, iteratedDeriv_one, Nat.factorial_one,
    Nat.cast_one, div_one, omittedSquareRootLift_forwardGerm R hR0, hg.deriv]
  linear_combination (1 / 2 : ℂ) * hd

/-- Every actual omitted point lies in the closed disk of radius two. -/
theorem exteriorOmitted_norm_le_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) : ‖P‖ ≤ 2 := by
  obtain ⟨R, hRa, hR0, hRpow⟩ :=
    exteriorOmitted_exists_normalized_analytic_root F hc hP
  have hclass := omittedSquareRootLift_centeredExteriorUnivalent F hc hP
    R hRa hR0 hRpow
  have harea := exteriorForwardCoeff_one_norm_le_of_finite_area
    (omittedSquareRootLift R)
    (fun N => exteriorForwardCoeff_finite_area _ hclass N)
  rw [omittedSquareRootLift_forwardCoeff_one F hc P R hRa hR0 hRpow,
    norm_div, norm_neg] at harea
  norm_num at harea
  linarith

end SpringerLean
