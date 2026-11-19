import SpringerLean.Round1324RealOppositeWitness
import SpringerLean.Round39RotateExterior
import SpringerLean.Round550RotateExterior

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- Explicit opposite projection point in the *original* ordinary
convex hull, obtained by rotating the first true omitted endpoint to
the positive real axis before evaluating the odd square root at ir. -/
theorem exteriorOmitted_opposite_hull_witness_of_first359
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hlarge : (359/180 : ℝ) < ‖P‖) (hP2 : ‖P‖ ≤ 2) :
    let ξ : ℂ := P/(‖P‖ : ℂ)
    ∃ w : ℂ, w ∈ convexHull ℝ (exteriorOmitted F) ∧
      (conj ξ*w).re < -(8/5 : ℝ) := by
  dsimp only
  let ξ : ℂ := P/(‖P‖ : ℂ)
  have hnorm : (0 : ℝ) < ‖P‖ := by linarith
  have hnorm0 : (‖P‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnorm)
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ]
    simp [norm_div, Complex.norm_real, abs_of_pos hnorm, ne_of_gt hnorm]
  have hξP : ξ*(‖P‖ : ℂ)=P := by
    dsimp [ξ]
    field_simp [hnorm0]
  let G := rotateExterior ξ F
  have hG : CenteredExteriorUnivalent G :=
    rotateExterior_centeredExteriorUnivalent F hc ξ hξ
  have hP_rot : (‖P‖ : ℂ) ∈ exteriorOmitted G := by
    apply (rotateExterior_omitted_iff F ξ hξ _).mpr
    simpa [hξP] using hP
  have hleft := actualHarmonic_neg24_25_re_lt_neg_eight_fifths
    G hG hlarge hP2 hP_rot
  let w : ℂ := actualHarmonic F (ξ * (-(24/25 : ℂ)))
  have hz : ‖ξ * (-(24/25 : ℂ))‖ < 1 := by
    rw [norm_mul,hξ,one_mul]
    norm_num
  have hw : w ∈ convexHull ℝ (exteriorOmitted F) :=
    actualHarmonic_mem_convexHull_omitted F hc hz
  have hrot := rotateExterior_actualHarmonic F ξ hξ (-(24/25 : ℂ))
  change actualHarmonic G (-(24/25 : ℂ)) = ξ⁻¹*w at hrot
  rw [hrot, Complex.inv_eq_conj hξ] at hleft
  exact ⟨w,hw,hleft⟩

end SpringerLean
