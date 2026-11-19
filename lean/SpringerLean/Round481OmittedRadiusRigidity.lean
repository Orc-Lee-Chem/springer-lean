import SpringerLean.Round480OmittedRadius
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace SpringerLean
set_option Elab.async false

theorem exteriorOmitted_convexHull_norm_le_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ convexHull ℝ (exteriorOmitted F)) : ‖P‖ ≤ 2 := by
  have hsub : exteriorOmitted F ⊆ Metric.closedBall (0 : ℂ) 2 := by
    intro w hw
    simpa using exteriorOmitted_norm_le_two F hc hw
  have hh := convexHull_min hsub (convex_closedBall (0 : ℂ) 2)
  simpa using hh hP

/-- An actual omitted point of radius two forces an actual slit map on E. -/
theorem exteriorOmitted_norm_eq_two_implies_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) (hP2 : ‖P‖ = 2) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk := by
  obtain ⟨R, hRa, hR0, hRpow⟩ :=
    exteriorOmitted_exists_normalized_analytic_root F hc hP
  let H := omittedSquareRootLift R
  have hclass : CenteredExteriorUnivalent H :=
    omittedSquareRootLift_centeredExteriorUnivalent F hc hP R hRa hR0 hRpow
  have hcoeff : exteriorForwardCoeff H 1 = -P / 2 :=
    omittedSquareRootLift_forwardCoeff_one F hc P R hRa hR0 hRpow
  have hfirst : ‖exteriorInverseCoeff H 1‖ = 1 := by
    rw [exteriorInverseCoeff_one_eq_forwardCoeff_one H hclass, hcoeff,
      norm_div, norm_neg, hP2]
    norm_num
  obtain ⟨a, ha, hHa⟩ :=
    (exteriorInverseCoeff_one_norm_eq_one_iff_slit H hclass).mp hfirst
  have hPa : P + 2 * a = 0 := by
    have he := exteriorForwardCoeff_eq_of_eqOn_exterior H (slitMap a) hHa 1
    rw [hcoeff, exteriorForwardCoeff_slitMap_one] at he
    linear_combination -2 * he
  refine ⟨a ^ 2, by rw [norm_pow, ha, one_pow], ?_⟩
  intro w hw
  obtain ⟨z, hz2⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < (2 : ℕ))
  have hz : z ∈ exteriorDisk := by
    have hn : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hz2]
    have hw1 : 1 < ‖w‖ := hw
    change 1 < ‖z‖
    nlinarith [norm_nonneg z]
  have hz0 := exterior_ne_zero hz
  have hs := omittedSquareRootLift_square F R P hRpow hz
  have heH : omittedSquareRootLift R z = slitMap a z := hHa hz
  rw [heH, hz2] at hs
  dsimp [slitMap] at hs ⊢
  have hw0 := exterior_ne_zero hw
  rw [← hz2] at hs ⊢
  field_simp [hz0] at hs ⊢
  linear_combination -hs + z ^ 2 * hPa

end SpringerLean
