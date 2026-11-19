import SpringerLean.Round20Contact
import SpringerLean.Round16Potential

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Unit rotation transfers the actual boundary logarithmic potential to
the unrotated exterior map at the rotated target value. -/
theorem regularExterior_rotated_boundary_potential_eq_unrotated
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (hξ : ‖ξ‖ = 1) (z : ℂ) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖z - conj ξ * rescaleExterior s F ζ‖) 0 1 =
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - ξ * z‖) 0 1 := by
  have hmul : ξ * conj ξ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    norm_num
  apply Real.circleAverage_congr_sphere
  intro ζ _
  apply congrArg Real.log
  calc
    ‖z - conj ξ * rescaleExterior s F ζ‖ =
        ‖ξ * (z - conj ξ * rescaleExterior s F ζ)‖ := by
          rw [norm_mul, hξ, one_mul]
    _ = ‖ξ * z - rescaleExterior s F ζ‖ := by
          congr 1
          rw [mul_sub, ← mul_assoc, hmul, one_mul]
    _ = ‖rescaleExterior s F ζ - ξ * z‖ := norm_sub_rev _ _

/-- The actual rotated regularized boundary logarithmic potential is
nonnegative at every complex target value. This uses the proven omitted-
value zero and image-value logarithm formulas, not a potential axiom. -/
theorem regularExterior_rotated_boundary_potential_nonneg
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (z : ℂ) :
    0 ≤ Real.circleAverage
      (fun ζ : ℂ => Real.log ‖z - conj ξ * rescaleExterior s F ζ‖) 0 1 := by
  rw [regularExterior_rotated_boundary_potential_eq_unrotated F s ξ hξ z]
  let G := rescaleExterior s F
  by_cases hImage : ξ * z ∈ G '' exteriorDisk
  · obtain ⟨v, hv, hvG⟩ := hImage
    have hpot := regularExterior_image_boundary_log_potential
      F hc hs0 hs1 hv
    change G v = ξ * z at hvG
    rw [← hvG]
    rw [hpot]
    exact Real.log_nonneg (le_of_lt hv)
  · have hOmitted : ξ * z ∈ exteriorOmitted G := hImage
    have hpot := regularExterior_omitted_boundary_log_potential_zero_all
      F hc hs0 hs1 hOmitted
    change 0 ≤ Real.circleAverage
      (fun ζ : ℂ => Real.log ‖G ζ - ξ * z‖) 0 1
    rw [hpot]

end SpringerLean
