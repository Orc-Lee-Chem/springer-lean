import SpringerLean.Round1323OppositeProjectionAlgebra
import SpringerLean.Round484RootOmittedSet
import SpringerLean.Round12HullParameter

namespace SpringerLean
set_option Elab.async false

/-- The imaginary square-root value supplies an actual point of the
ordinary omitted-set hull to the left of -8/5 when the first omitted
endpoint lies past 359/180. -/
theorem actualHarmonic_neg24_25_re_lt_neg_eight_fifths
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR : (359/180 : ℝ) < R) (hR2 : R ≤ 2)
    (hP : (R : ℂ) ∈ exteriorOmitted F) :
    (actualHarmonic F (-(24/25 : ℂ))).re < -(8/5 : ℝ) := by
  obtain ⟨H,hH,ho,hb,hsquare,_⟩ :=
    exteriorOmitted_exists_root_with_omitted_set F hc hP
  let r : ℝ := largeRootRadius
  let A : ℝ := R/2
  let M : ℝ := r+A/r
  let T : ℂ := H (Complex.I*(r : ℂ))-Complex.I*(M : ℂ)
  have hR0 : 0 ≤ R := by linarith
  have hA : (359/360 : ℝ) < A := by dsimp [A]; linarith
  have hdef : 1-A^2 < (1/180 : ℝ) := by
    have hAsq : (359/360 : ℝ)^2 < A^2 :=
      (sq_lt_sq₀ (by norm_num) (by dsimp [A]; linarith)).mpr hA
    nlinarith [hAsq]
  have hT : ‖T‖ < (3/40 : ℝ) := by
    simpa [T,M,A,r] using
      odd_root_imaginary_tail_lt_three_fortieths H hH ho hR0 hR2 hb
        (by simpa [A] using hdef)
  have hM0 : 0 ≤ M := by
    have hr0 : 0 ≤ r := by dsimp [r]; linarith [largeRootRadius_gt_one]
    have hA0 : 0 ≤ A := by linarith
    dsimp [M]
    exact add_nonneg hr0 (div_nonneg hA0 hr0)
  have hM : M ≤ (49/24 : ℝ) := by
    exact largeRootM_le_49_24 hR0 hR2
  have hAcast : (R : ℂ)/2 = (A : ℂ) := by
    dsimp [A]
    push_cast
    ring
  have hMcast : (r : ℂ)+(R : ℂ)/2/(r : ℂ) = (M : ℂ) := by
    dsimp [M,A]
    push_cast
    ring
  have hid := actualHarmonic_neg24_25_odd_root_identity F H R hsquare
  change actualHarmonic F (-(24/25 : ℂ)) =
    -(1+((R : ℂ)/2)^2)*(24/25 : ℂ)+
      2*Complex.I*((r : ℂ)+(R : ℂ)/2/(r : ℂ))*
        (H (Complex.I*(r : ℂ))-
          Complex.I*((r : ℂ)+(R : ℂ)/2/(r : ℂ)))+
      (H (Complex.I*(r : ℂ))-
          Complex.I*((r : ℂ)+(R : ℂ)/2/(r : ℂ)))^2 at hid
  rw [hMcast,hAcast] at hid
  change actualHarmonic F (-(24/25 : ℂ)) =
    -(1+(A : ℂ)^2)*(24/25 : ℂ)+2*Complex.I*(M : ℂ)*T+T^2 at hid
  rw [hid]
  exact imaginary_root_projection_lt_neg_eight_fifths A M T hA hM0 hM hT

theorem actualHarmonic_neg24_25_hull_witness
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR : (359/180 : ℝ) < R) (hR2 : R ≤ 2)
    (hP : (R : ℂ) ∈ exteriorOmitted F) :
    ∃ w : ℂ, w ∈ convexHull ℝ (exteriorOmitted F) ∧
      w.re < -(8/5 : ℝ) := by
  let w := actualHarmonic F (-(24/25 : ℂ))
  refine ⟨w, ?_, actualHarmonic_neg24_25_re_lt_neg_eight_fifths F hc hR hR2 hP⟩
  apply actualHarmonic_mem_convexHull_omitted F hc
  norm_num [w]

end SpringerLean
