import SpringerLean.Round635ExplicitRootStrip
import SpringerLean.Round550RotateExterior

namespace SpringerLean
set_option Elab.async false

/-- The explicit strip in any unit direction, for the actual ordinary
convex hull. Rotating coordinates also rotates the source of the same F. -/
theorem exteriorOmitted_convexHull_explicit_rotated_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (a : ℂ) (ha : ‖a‖ = 1) {R r : ℝ}
    (hR0 : 0 ≤ R) (hR2 : R ≤ 2)
    (hP : a*(R : ℂ) ∈ exteriorOmitted F) (hr : 1 < r)
    {w : ℂ} (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    (a⁻¹*w).im^2 ≤ 4*(exteriorRealRootWidth R r)^2*
      ((exteriorRealRootWidth R r)^2+R-(a⁻¹*w).re) ∧
    ‖w‖^2 ≤ ((a⁻¹*w).re-2*(exteriorRealRootWidth R r)^2)^2+
      4*(exteriorRealRootWidth R r)^2*R := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let T : ℂ →ₗ[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ a⁻¹).toLinearMap
  have himage : T '' exteriorOmitted F = exteriorOmitted (rotateExterior a F) := by
    ext q
    constructor
    · rintro ⟨v,hv,rfl⟩
      apply (rotateExterior_omitted_iff F a ha _).mpr
      simpa [T,mul_assoc,ha0] using hv
    · intro hq
      refine ⟨a*q,(rotateExterior_omitted_iff F a ha q).mp hq,?_⟩
      simp [T,mul_assoc,ha0]
  have htw : T w ∈ convexHull ℝ (exteriorOmitted (rotateExterior a F)) := by
    rw [← himage,← T.image_convexHull]
    exact ⟨w,hw,rfl⟩
  have hPr : (R : ℂ) ∈ exteriorOmitted (rotateExterior a F) :=
    (rotateExterior_omitted_iff F a ha _).mpr hP
  have hs := exteriorOmitted_convexHull_explicit_real_strip
    (rotateExterior a F) (rotateExterior_centeredExteriorUnivalent F hc a ha)
    hR0 hR2 hPr hr htw
  have hnorm : ‖T w‖ = ‖w‖ := by
    change ‖a⁻¹*w‖=‖w‖
    rw [norm_mul,norm_inv,ha,inv_one,one_mul]
  rw [hnorm] at hs
  simpa [T] using hs

end SpringerLean
