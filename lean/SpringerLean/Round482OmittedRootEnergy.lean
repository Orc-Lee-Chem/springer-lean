import SpringerLean.Round481OmittedRadiusRigidity
import SpringerLean.Round69WeightedArea

namespace SpringerLean
set_option Elab.async false

theorem exteriorForwardCoeff_even_eq_zero_of_odd
    (H : ℂ → ℂ) (hodd : ∀ z, H (-z) = -H z) (k : ℕ) :
    exteriorForwardCoeff H (2 * k) = 0 := by
  let g := exteriorForwardGerm H
  have hg : ∀ u, g (-u) = -g u := by
    intro u
    by_cases hu : u = 0
    · simp [g, hu, exteriorForwardGerm_zero]
    · simp [g, exteriorForwardGerm, hu, hodd]
      ring
  have hfun : (fun u : ℂ => g (-u)) = (fun u => -g u) := funext hg
  have hd := iteratedDeriv_comp_neg (2 * k) g (0 : ℂ)
  rw [hfun, iteratedDeriv_fun_neg] at hd
  simp only [neg_zero, smul_eq_mul, pow_mul, neg_one_sq, one_pow, one_mul] at hd
  have hz : iteratedDeriv (2 * k) g 0 = 0 := by linear_combination (-1 / 2 : ℂ) * hd
  change iteratedDeriv (2 * k) g 0 / _ = 0
  rw [hz, zero_div]

/-- The full actual square-root input to the strip proof: oddness, first
coefficient, square identity and every finite remaining area budget. -/
theorem exteriorOmitted_exists_odd_root_with_energy
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) :
    ∃ H : ℂ → ℂ, CenteredExteriorUnivalent H ∧
      (∀ z, H (-z) = -H z) ∧
      exteriorForwardCoeff H 1 = -P / 2 ∧
      (∀ k : ℕ, exteriorForwardCoeff H (2 * k) = 0) ∧
      (∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - P) ∧
      ∀ N : ℕ, 1 ≤ N →
        (∑ j ∈ Finset.Icc 2 N, (j : ℝ) * ‖exteriorForwardCoeff H j‖ ^ 2) ≤
          1 - ‖P‖ ^ 2 / 4 := by
  obtain ⟨R, hRa, hR0, hRpow⟩ :=
    exteriorOmitted_exists_normalized_analytic_root F hc hP
  let H := omittedSquareRootLift R
  have hclass : CenteredExteriorUnivalent H :=
    omittedSquareRootLift_centeredExteriorUnivalent F hc hP R hRa hR0 hRpow
  have hodd : ∀ z, H (-z) = -H z := omittedSquareRootLift_odd R
  have hcoeff : exteriorForwardCoeff H 1 = -P / 2 :=
    omittedSquareRootLift_forwardCoeff_one F hc P R hRa hR0 hRpow
  refine ⟨H, hclass, hodd, hcoeff,
    exteriorForwardCoeff_even_eq_zero_of_odd H hodd, ?_, ?_⟩
  · exact fun z hz => omittedSquareRootLift_square F R P hRpow hz
  · intro N hN
    have ht := exteriorForwardCoeff_finite_area_tail H hclass N hN
    rw [hcoeff, norm_div, norm_neg] at ht
    norm_num at ht
    convert ht using 1 <;> ring

end SpringerLean
