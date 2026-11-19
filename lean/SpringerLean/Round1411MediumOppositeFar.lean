import SpringerLean.Round1410MediumChordScalar
import SpringerLean.Round1336CoarseActualGeometry

open scoped ComplexConjugate

namespace SpringerLean

/-- A hull point of radius at least 1.9 behind a radius-maximal end
must take the far chord branch; the two-point estimate also controls
its sum with that endpoint. -/
theorem exteriorOmitted_opposite_half_far_451_100
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P w ξ : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ : ‖ξ‖ = 1)
    (hPform : P = ξ*(‖P‖:ℂ))
    (hPbig : (19/10 : ℝ) ≤ ‖P‖)
    (hwr : (19/10 : ℝ) ≤ ‖w‖)
    (hmax : ‖w‖ ≤ ‖P‖)
    (hopp : (conj ξ*w).re ≤ 0) :
    let e : ℝ := 2-‖w‖
    4-‖w-P‖ ≤ (451/100 : ℝ)*e ∧
    ‖w+P‖^2 ≤ 4*(451/100 : ℝ)*e := by
  dsimp only
  let e : ℝ := 2-‖w‖
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/10 := by dsimp [e]; linarith
  have hcos := complex_chord_projection_identity w P ξ ‖P‖ hξ hPform
  have hR2 : (19/10 : ℝ)^2 ≤ ‖P‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg P)).mpr hPbig
  have hw2' : (19/10 : ℝ)^2 ≤ ‖w‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg w)).mpr hwr
  have hterm : 0 ≤ -2*‖P‖*(conj ξ*w).re := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by nlinarith [norm_nonneg P]) hopp
  have hnearImpossible : ¬ ‖w-P‖ ≤ (451/100 : ℝ)*e := by
    intro hnear
    have hu0 : 0 ≤ ‖w-P‖ := norm_nonneg _
    have husmall : ‖w-P‖ ≤ (451/1000 : ℝ) := by linarith
    have husq : ‖w-P‖^2 ≤ (451/1000 : ℝ)^2 :=
      (sq_le_sq₀ hu0 (by norm_num)).mpr husmall
    nlinarith [hcos,hR2,hw2',hterm]
  have hpair := exteriorOmitted_pair_distance_deficit F hc w P
    hw hP he0 (by linarith) (by dsimp [e]; linarith)
    (by dsimp [e]; linarith)
  have hu4 : ‖w-P‖ ≤ 4 := by
    calc
      ‖w-P‖ ≤ ‖w‖+‖P‖ := norm_sub_le _ _
      _ ≤ 4 := by
        have hP2 := exteriorOmitted_convexHull_norm_le_two F hc hP
        linarith
  have hfar : 4-‖w-P‖ ≤ (451/100 : ℝ)*e := by
    have hpair' : ‖w-P‖*(4-‖w-P‖) ≤ 16*e := by
      nlinarith [sq_nonneg e]
    rcases twoPoint_near_far_451_100 he0 heδ (norm_nonneg _) hu4
      hpair' with hnear | hfar
    · exact False.elim (hnearImpossible hnear)
    · exact hfar
  have htwo := exteriorOmitted_convexHull_two_point F hc w P hw hP
  constructor
  · exact hfar
  · nlinarith [htwo]

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_opposite_half_far_451_100
