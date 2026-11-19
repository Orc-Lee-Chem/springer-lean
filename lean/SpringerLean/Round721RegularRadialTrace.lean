import SpringerLean.Round719ActualAngularMajorant
import SpringerLean.Round697ActualDiskLipschitz
import SpringerLean.RescaleGerm

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Both fillings are built from the same actual forward germ.  The
identity is global, and does not extend an EqOn assertion about F itself. -/
theorem actualHarmonic_rescale_eq_regular (s : ℝ) (hs : 0 < s) (F : ℂ → ℂ) :
    actualHarmonic (rescaleExterior s F) = regularHarmonic s F := by
  funext z
  change z+exteriorForwardGerm (rescaleExterior s F) (conj z) =
    z+(s : ℂ)*exteriorForwardGerm F ((s : ℂ)*conj z)
  rw [rescaleExterior_forwardGerm s hs F]

theorem regularHarmonic_exists_closed_disk_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ closedBall (0 : ℂ) 1,
      ∀ v ∈ closedBall (0 : ℂ) 1,
        ‖regularHarmonic s F u-regularHarmonic s F v‖ ≤ L*‖u-v‖ := by
  obtain ⟨M, hM0, hM⟩ := exteriorForwardGerm_exists_disk_lipschitz F hc hs0.le hs1
  refine ⟨1+s^2*M, by positivity, ?_⟩
  intro u hu v hv
  have harg {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
      (s : ℂ)*conj z ∈ closedBall (0 : ℂ) s := by
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_conj]
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith
  have hg := hM _ (harg hu) _ (harg hv)
  have hdiff : ‖(s : ℂ)*conj u-(s : ℂ)*conj v‖ = s*‖u-v‖ := by
    rw [← mul_sub, ← map_sub, norm_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  rw [hdiff] at hg
  have heq : regularHarmonic s F u-regularHarmonic s F v =
      (u-v)+(s : ℂ)*(exteriorForwardGerm F ((s : ℂ)*conj u)-
        exteriorForwardGerm F ((s : ℂ)*conj v)) := by
    simp only [regularHarmonic, regularForwardGerm]
    ring
  rw [heq]
  calc
    _ ≤ ‖u-v‖+‖(s : ℂ)*(exteriorForwardGerm F ((s : ℂ)*conj u)-
        exteriorForwardGerm F ((s : ℂ)*conj v))‖ := norm_add_le _ _
    _ = ‖u-v‖+s*‖exteriorForwardGerm F ((s : ℂ)*conj u)-
        exteriorForwardGerm F ((s : ℂ)*conj v)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    _ ≤ ‖u-v‖+s*(M*(s*‖u-v‖)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hg hs0.le)
    _ = (1+s^2*M)*‖u-v‖ := by ring

/-- Uniform radial approach to the ACTUAL regularized boundary.  One
constant works for every angle, direction and radius in the closed disk. -/
theorem regularHarmonic_angular_boundary_exists_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (c : ℂ) (r : ℝ), r ∈ Icc 0 1 → ∀ θ : ℝ,
      |(c*regularHarmonic s F (circleMap 0 r θ)).re-
        (c*rescaleExterior s F (circleMap 0 1 θ)).re| ≤ ‖c‖*L*(1-r) := by
  obtain ⟨L, hL0, hL⟩ := regularHarmonic_exists_closed_disk_lipschitz F hc hs0 hs1
  refine ⟨L, hL0, ?_⟩
  intro c r hr θ
  have hu : circleMap 0 r θ ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr.1] using hr.2
  have hv : circleMap 0 1 θ ∈ closedBall (0 : ℂ) 1 := by
    simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_one, le_refl]
  have hg := hL _ hu _ hv
  have hunit : regularHarmonic s F (circleMap 0 1 θ) =
      rescaleExterior s F (circleMap 0 1 θ) :=
    regularHarmonic_unitCircle_eq_actual F hs0 (by simp [norm_circleMap_zero])
  rw [hunit] at hg
  have hd : circleMap 0 r θ-circleMap 0 1 θ = circleMap 0 (r-1) θ := by
    simp only [circleMap_zero, Complex.ofReal_sub, sub_mul]
  rw [hd, norm_circleMap_zero, abs_of_nonpos (sub_nonpos.mpr hr.2)] at hg
  have heq : (c*regularHarmonic s F (circleMap 0 r θ)).re-
      (c*rescaleExterior s F (circleMap 0 1 θ)).re =
      (c*(regularHarmonic s F (circleMap 0 r θ)-
        rescaleExterior s F (circleMap 0 1 θ))).re := by
    simp only [mul_sub, Complex.sub_re]
  rw [heq]
  calc
    _ ≤ ‖c*(regularHarmonic s F (circleMap 0 r θ)-
        rescaleExterior s F (circleMap 0 1 θ))‖ := Complex.abs_re_le_norm _
    _ = ‖c‖*‖regularHarmonic s F (circleMap 0 r θ)-
        rescaleExterior s F (circleMap 0 1 θ)‖ := norm_mul _ _
    _ ≤ ‖c‖*(L*(-(r-1))) := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = ‖c‖*L*(1-r) := by ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_rescale_eq_regular
#print axioms SpringerLean.regularHarmonic_exists_closed_disk_lipschitz
#print axioms SpringerLean.regularHarmonic_angular_boundary_exists_lipschitz
