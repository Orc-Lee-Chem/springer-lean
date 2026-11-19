import SpringerLean.Round1318Catalan359Scalar
import SpringerLean.Round659OmittedRadiusCoefficient
import SpringerLean.Round480OmittedRadius

namespace SpringerLean
set_option Elab.async false

/-- The actual Catalan candidate forces the first omitted endpoint close
enough to radius two to leave less than 1/180 of odd-root area budget.
The candidate includes equality and no boundary trace is assumed. -/
theorem exteriorOmitted_exists_candidate_first_endpoint359
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ P : ℂ, P ∈ exteriorOmitted F ∧
      (359/180 : ℝ) < ‖P‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P‖) ∧
      ‖P‖ ≤ 2 ∧
      0 ≤ 1-(‖P‖/2)^2 ∧
      1-(‖P‖/2)^2 < (1/180 : ℝ) := by
  obtain ⟨P,hP,hmax,hbudget⟩ :=
    exteriorOmitted_exists_maximizer_with_inverseCoeff_budget F hc
  have hn : 1 ≤ 2*k-1 := by omega
  have hid : 2*(k-1)+1=2*k-1 := by omega
  have hscalar := scaledCatalanMoment_cutoff359 (k-1) (by omega)
  have hform : scaledCatalanMoment (k-1) =
      (((2*(k-1)+1 : ℕ) : ℝ))*(catalan (k-1) : ℝ) := by
    simp [scaledCatalanMoment]
  rw [hform,hid] at hscalar
  have hcandidate := mul_le_mul_of_nonneg_left hB
    (Nat.cast_nonneg (2*k-1) : (0 : ℝ) ≤ (2*k-1 : ℕ))
  have hcoef := hbudget (2*k-1) hn
  have hlarge : (359/180 : ℝ) < ‖P‖ := by
    by_contra h
    have hp := pow_le_pow_left₀ (norm_nonneg P) (le_of_not_gt h) (2*k-1)
    linarith
  have hnorm := exteriorOmitted_norm_le_two F hc hP
  have hA : (359/360 : ℝ) < ‖P‖/2 := by linarith
  have hA1 : ‖P‖/2 ≤ 1 := by linarith
  have hA0 : 0 ≤ ‖P‖/2 := by positivity
  have hsq : (359/360 : ℝ)^2 < (‖P‖/2)^2 :=
    (sq_lt_sq₀ (by norm_num) hA0).mpr hA
  refine ⟨P,hP,hlarge,hmax,hnorm,?_,?_⟩
  · nlinarith
  · nlinarith [hsq]

end SpringerLean
