import SpringerLean.Round602RootMidpointEnergy

namespace SpringerLean
set_option Elab.async false

theorem exteriorReciprocalCoeff_one
    (V : ℂ → ℂ) (hV : CenteredExteriorUnivalent V) :
    exteriorReciprocalCoeff V 1 = 1 := by
  have hden := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add
    ((hasDerivAt_id (0 : ℂ)).mul hV.2.2.differentiableAt.hasDerivAt)
  have hd := (hasDerivAt_id (0 : ℂ)).div hden (by simp)
  have hfun : (id / ((fun _ : ℂ => (1 : ℂ)) + id * exteriorForwardGerm V)) =
      exteriorReciprocalGerm V := by
    funext u
    rfl
  rw [hfun] at hd
  have hderiv : deriv (exteriorReciprocalGerm V) 0 = 1 := by
    simpa using hd.deriv
  simpa only [exteriorReciprocalCoeff, actualTaylorCoeff, iteratedDeriv_one,
    Nat.factorial_one, Nat.cast_one, div_one] using hderiv

/-- Actual-F version of the finite reciprocal-energy budget in the corrected
two-point proof. All square-root and midpoint hypotheses are constructed here. -/
theorem exteriorOmitted_exists_midpoint_reciprocal_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ exteriorOmitted F) (hP : P ∈ exteriorOmitted F) (hAP : A ≠ P) :
    ∃ V : ℂ → ℂ, CenteredExteriorUnivalent V ∧
      (∀ z ∈ exteriorDisk, V z ≠ 0) ∧
      exteriorForwardCoeff V 1 = -(A + P) / 4 ∧
      exteriorReciprocalCoeff V 1 = 1 ∧
      ∀ N : ℕ,
        (∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ‖exteriorForwardCoeff V j‖ ^ 2) +
          (‖P - A‖ / 4) ^ 2 *
            (∑ j ∈ Finset.Icc 1 N, (j : ℝ) * ‖exteriorReciprocalCoeff V j‖ ^ 2) ≤ 1 := by
  obtain ⟨H, J, hH, hJ, _, _, hsH, hsJ, hV, hbV, hrec⟩ :=
    exteriorOmitted_exists_root_midpoint F hc A P hA hP hAP
  have hq : (P - A) / 4 ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hAP.symm) (by norm_num)
  have hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * ((P - A) / 4) := by
    intro z hz
    rw [hsH z hz, hsJ z hz]
    ring
  refine ⟨exteriorRootMidpoint H J, hV, fun z hz => (hrec z hz).1, hbV,
    exteriorReciprocalCoeff_one _ hV, ?_⟩
  intro N
  have he := exteriorRootMidpoint_finite_reciprocal_energy H J hH hJ _ hq hs N
  simpa only [norm_div, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] using he

end SpringerLean
