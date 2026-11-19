import SpringerLean.Round1336CoarseActualGeometry

open scoped ComplexConjugate

namespace SpringerLean

/-- A high-radius hull point behind an endpoint must take the far chord
branch. The same two-point inequality then places its *sum* with the
endpoint in a ball of squared radius `17e`. -/
theorem exteriorOmitted_opposite_half_far_17_4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P w ξ : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ : ‖ξ‖ = 1)
    (hPform : P = ξ * (‖P‖ : ℂ))
    (hPbig : (39/20 : ℝ) ≤ ‖P‖)
    (hwr : (39/20 : ℝ) ≤ ‖w‖)
    (hmax : ‖w‖ ≤ ‖P‖)
    (hopp : (conj ξ * w).re ≤ 0) :
    let e : ℝ := 2 - ‖w‖
    4 - ‖w-P‖ ≤ (17/4 : ℝ)*e ∧
      ‖w+P‖^2 ≤ 17*e := by
  dsimp only
  let e : ℝ := 2 - ‖w‖
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/20 := by dsimp [e]; linarith
  have hcos := complex_chord_projection_identity w P ξ ‖P‖ hξ hPform
  have hR2 : (39/20 : ℝ)^2 ≤ ‖P‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg P)).mpr hPbig
  have hw2' : (39/20 : ℝ)^2 ≤ ‖w‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg w)).mpr hwr
  have hterm : 0 ≤ -2*‖P‖*(conj ξ*w).re := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by nlinarith [norm_nonneg P]) hopp
  have hnearImpossible : ¬ ‖w-P‖ ≤ (17/4 : ℝ)*e := by
    intro hnear
    have hu0 : 0 ≤ ‖w-P‖ := norm_nonneg _
    have husmall : ‖w-P‖ ≤ 17/80 := by linarith
    have husq : ‖w-P‖^2 ≤ (17/80 : ℝ)^2 :=
      (sq_le_sq₀ hu0 (by norm_num)).mpr husmall
    nlinarith [hcos, hR2, hw2', hterm]
  have hfar : 4 - ‖w-P‖ ≤ (17/4 : ℝ)*e := by
    rcases exteriorOmitted_hull_near_far_17_4 F hc w P hw hP
      he0 heδ (by dsimp [e]; linarith)
      (by dsimp [e]; linarith) with hnear | hfar
    · exact False.elim (hnearImpossible hnear)
    · exact hfar
  have htwo := exteriorOmitted_convexHull_two_point F hc w P hw hP
  constructor
  · exact hfar
  · nlinarith [htwo]

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_opposite_half_far_17_4
