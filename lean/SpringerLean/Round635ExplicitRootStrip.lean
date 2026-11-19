import SpringerLean.Round634RealRootCircleWidth
import SpringerLean.Round543RootCircleStrip

namespace SpringerLean
set_option Elab.async false

/-- Corrected br:strip for a real nonnegative actual omitted point. The
width is explicit and comes from the same map's odd-root coefficients. -/
theorem exteriorOmitted_convexHull_explicit_real_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R r : ℝ} (hR0 : 0 ≤ R) (hR2 : R ≤ 2)
    (hP : (R : ℂ) ∈ exteriorOmitted F) (hr : 1 < r)
    {w : ℂ} (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    w.im^2 ≤ 4*(exteriorRealRootWidth R r)^2*
      ((exteriorRealRootWidth R r)^2+R-w.re) ∧
    ‖w‖^2 ≤ (w.re-2*(exteriorRealRootWidth R r)^2)^2+
      4*(exteriorRealRootWidth R r)^2*R := by
  obtain ⟨H,hH,ho,hb,hsquare,hK⟩ :=
    exteriorOmitted_exists_root_with_omitted_set F hc hP
  let M := exteriorRealRootWidth R r
  have hM : 0 ≤ M := exteriorRealRootWidth_nonneg hR0 hR2 hr
  have hbound : ∀ u ∈ exteriorOmitted H, |u.re| ≤ M := by
    intro u hu
    obtain ⟨z,hz,hpos⟩ := exteriorOmitted_projection_circle_witness H hH hr 1 hu
    obtain ⟨v,hv,hneg⟩ := exteriorOmitted_projection_circle_witness H hH hr (-1) hu
    simp only [one_mul] at hpos
    simp only [neg_one_mul,Complex.neg_re] at hneg
    have hzp := exterior_real_odd_root_circle_re_abs_le H hH ho hR0 hR2 hr hb hz
    have hvp := exterior_real_odd_root_circle_re_abs_le H hH ho hR0 hR2 hr hb hv
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs (H v).re]
    · exact hpos.trans ((le_abs_self _).trans hzp)
  have hroot : ∀ q ∈ exteriorOmitted F,
      ∃ v : ℂ, v^2=q-(R : ℂ) ∧ v.re^2 ≤ M^2 := by
    intro q hq
    obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (q-(R : ℂ)) (by norm_num : 0 < (2 : ℕ))
    have hvK : v ∈ exteriorOmitted H := (hK v).mpr (by simpa [hv] using hq)
    have hvb := hbound v hvK
    refine ⟨v,hv,?_⟩
    have hh := (sq_le_sq₀ (abs_nonneg v.re) hM).mpr hvb
    simpa only [sq_abs] using hh
  have hhull := convexHull_subset_parabolicStrip_of_root_bound
    (exteriorOmitted F) (sq_nonneg M) hroot
  have hs : w.im^2 ≤ 4*M^2*(M^2+R-w.re) := hhull hw
  refine ⟨hs,?_⟩
  have hn : ‖w‖^2=w.re^2+w.im^2 := by
    simpa [Complex.normSq_apply,pow_two] using Complex.sq_norm w
  change ‖w‖^2 ≤ (w.re-2*M^2)^2+4*M^2*R
  nlinarith

end SpringerLean
