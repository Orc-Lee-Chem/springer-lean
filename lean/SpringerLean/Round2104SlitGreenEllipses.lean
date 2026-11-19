import SpringerLean.Round2102GreenAngularLevels
import SpringerLean.Round2043EvenStarSlitGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Set Real

namespace SpringerLean

private theorem norm_add_two_sq (z : ℂ) : ‖z+2‖^2 = ‖z‖^2 + 4 + 4*z.re := by
  rw [←Complex.normSq_eq_norm_sq, ←Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.add_re,Complex.add_im]
  ring

private theorem norm_sub_two_sq (z : ℂ) : ‖z-2‖^2 = ‖z‖^2 + 4 - 4*z.re := by
  rw [←Complex.normSq_eq_norm_sq, ←Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

/-- Confocal ellipses are the level curves of the actual slit Green
coordinate. The formula remains valid on the slit itself. -/
theorem slitGreen_cosh_eq_focal_distances (z : ℂ) :
    Real.cosh (exteriorGreenCoordinate (slitMap 1) z) = (‖z-2‖+‖z+2‖)/4 := by
  classical
  let F := slitMap 1
  have hF := slitMap_centeredExteriorUnivalent 1 (by simp)
  by_cases hz : z ∈ F '' exteriorDisk
  · obtain ⟨w,hw,rfl⟩ := hz
    have h0 := exterior_ne_zero hw
    have hwr : 0 < ‖w‖ := norm_pos_iff.mpr h0
    have hmem : F w ∈ F '' exteriorDisk := ⟨w,hw,rfl⟩
    have hinv : exteriorInverse F (F w) = w := hF.2.1.leftInvOn_invFunOn hw
    have hplus : F w + 2 = (w+1)^2/w := by
      dsimp [F,slitMap]
      field_simp [h0]
      <;> ring
    have hminus : F w - 2 = (w-1)^2/w := by
      dsimp [F,slitMap]
      field_simp [h0]
      <;> ring
    have hsum : ‖w-1‖^2+‖w+1‖^2 = 2*(‖w‖^2+1) := by
      simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
        Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im]
      ring
    change Real.cosh (exteriorGreenCoordinate F (F w)) = _
    rw [exteriorGreenCoordinate, if_pos hmem, hinv, Real.cosh_eq, Real.exp_neg, Real.exp_log hwr,
      hplus,hminus,norm_div,norm_div,norm_pow,norm_pow, ←add_div,hsum]
    field_simp [hwr.ne']
    <;> ring
  · have hL : z ∈ {w : ℂ | w.im=0 ∧ -2≤w.re ∧ w.re≤2} := by
      rw [←slitMap_one_omitted_eq_segment]
      exact hz
    obtain ⟨hz0,hlo,hhi⟩ := hL
    have he : z = (z.re:ℂ) := Complex.ext (by simp) (by simpa using hz0)
    have hminus : ‖z-2‖ = 2-z.re := by
      rw [show z-2 = ((z.re-2:ℝ):ℂ) by rw [Complex.ofReal_sub]; simpa using he,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hhi)]
      ring
    have hplus : ‖z+2‖ = z.re+2 := by
      rw [show z+2 = ((z.re+2:ℝ):ℂ) by rw [Complex.ofReal_add]; simpa using he,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    change Real.cosh (exteriorGreenCoordinate F z) = _
    rw [exteriorGreenCoordinate, if_neg hz, Real.cosh_zero, hminus,hplus]
    ring

/-- On each fixed centered circle, the slit Green coordinate decreases
as the absolute real part increases. In angular coordinates centered on
the imaginary axis, its top sets are centered arcs. -/
theorem slitGreen_antitone_abs_re_of_norm_eq (z w : ℂ)
    (hN : ‖z‖ = ‖w‖) (hRe : |w.re| ≤ |z.re|) :
    exteriorGreenCoordinate (slitMap 1) z ≤ exteriorGreenCoordinate (slitMap 1) w := by
  have hab : w.re^2 ≤ z.re^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg w.re) hRe 2
    simpa only [sq_abs] using h
  have hp (v : ℂ) : (‖v-2‖*‖v+2‖)^2 = (‖v‖^2+4)^2-16*v.re^2 := by
    rw [mul_pow,norm_sub_two_sq,norm_add_two_sq]
    ring
  have hdprod : ‖z-2‖*‖z+2‖ ≤ ‖w-2‖*‖w+2‖ := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [hp,hp,hN]
    linarith only [hab]
  have hs (v : ℂ) : (‖v-2‖+‖v+2‖)^2 = 2*(‖v‖^2+4)+2*(‖v-2‖*‖v+2‖) := by
    rw [add_sq,norm_sub_two_sq,norm_add_two_sq]
    ring
  have hdsum : ‖z-2‖+‖z+2‖ ≤ ‖w-2‖+‖w+2‖ := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [hs,hs,hN]
    linarith only [hdprod]
  have hg : Real.cosh (exteriorGreenCoordinate (slitMap 1) z) ≤
      Real.cosh (exteriorGreenCoordinate (slitMap 1) w) := by
    rw [slitGreen_cosh_eq_focal_distances,slitGreen_cosh_eq_focal_distances]
    linarith only [hdsum]
  simpa only [abs_of_nonneg (exteriorGreenCoordinate_nonneg _ _)] using Real.cosh_le_cosh.mp hg

end SpringerLean
