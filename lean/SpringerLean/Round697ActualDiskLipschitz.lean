import SpringerLean.Round686ActualAngularOptimizer
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The derivative bound is obtained from actual analyticity on a larger
disk and compactness. It is not an added hypothesis on the paper's class. -/
theorem exteriorForwardGerm_exists_disk_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ closedBall (0 : ℂ) R,
      ∀ v ∈ closedBall (0 : ℂ) R,
        ‖exteriorForwardGerm F u-exteriorForwardGerm F v‖ ≤ L*‖u-v‖ := by
  have hA := exteriorForwardGerm_analyticOnNhd_unitBall F hc
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  have hdc : ContinuousOn (deriv (exteriorForwardGerm F)) (closedBall (0 : ℂ) R) :=
    hA.deriv.continuousOn.mono hsub
  have hb : Bornology.IsBounded (deriv (exteriorForwardGerm F) '' closedBall (0 : ℂ) R) :=
    ((isCompact_closedBall (0 : ℂ) R).image_of_continuousOn hdc).isBounded
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  let L : ℝ := max M 0
  have hL0 : 0 ≤ L := le_max_right _ _
  have hd : ∀ z ∈ closedBall (0 : ℂ) R, ‖deriv (exteriorForwardGerm F) z‖ ≤ L := by
    intro z hz
    exact (hM _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  refine ⟨L, hL0, ?_⟩
  intro u hu v hv
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hA z (hsub hz)).differentiableAt) hd
    (convex_closedBall (0 : ℂ) R) hv hu

/-- A local Lipschitz constant for the actual harmonic filling, uniformly
on any fixed closed subdisk. -/
theorem actualHarmonic_exists_disk_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ closedBall (0 : ℂ) R,
      ∀ v ∈ closedBall (0 : ℂ) R,
        ‖actualHarmonic F u-actualHarmonic F v‖ ≤ L*‖u-v‖ := by
  obtain ⟨M, hM0, hM⟩ := exteriorForwardGerm_exists_disk_lipschitz F hc hR0 hR1
  refine ⟨1+M, by linarith, ?_⟩
  intro u hu v hv
  have hcu : conj u ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hu
  have hcv : conj v ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hv
  have hg := hM (conj u) hcu (conj v) hcv
  have hnorm : ‖conj u-conj v‖ = ‖u-v‖ := by
    rw [← map_sub, Complex.norm_conj]
  rw [hnorm] at hg
  have heq : actualHarmonic F u-actualHarmonic F v =
      (u-v)+(exteriorForwardGerm F (conj u)-exteriorForwardGerm F (conj v)) := by
    simp only [actualHarmonic]
    ring
  rw [heq]
  calc
    ‖(u-v)+(exteriorForwardGerm F (conj u)-exteriorForwardGerm F (conj v))‖ ≤
        ‖u-v‖+‖exteriorForwardGerm F (conj u)-exteriorForwardGerm F (conj v)‖ :=
      norm_add_le _ _
    _ ≤ ‖u-v‖+M*‖u-v‖ := by linarith
    _ = (1+M)*‖u-v‖ := by ring

/-- Uniform radial stability of each actual projection. The SAME constant
works for every angle and direction, with the direction's norm explicit. -/
theorem actualHarmonic_angular_projection_exists_radius_lipschitz
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r ∈ Icc 0 R, ∀ r' ∈ Icc 0 R, ∀ (c : ℂ) (θ : ℝ),
      |(c*actualHarmonic F (circleMap 0 r θ)).re-
        (c*actualHarmonic F (circleMap 0 r' θ)).re| ≤ ‖c‖*L*|r-r'| := by
  obtain ⟨L, hL0, hL⟩ := actualHarmonic_exists_disk_lipschitz F hc hR0 hR1
  refine ⟨L, hL0, ?_⟩
  intro r hr r' hr' c θ
  have hu : circleMap 0 r θ ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr.1] using hr.2
  have hv : circleMap 0 r' θ ∈ closedBall (0 : ℂ) R := by
    simpa only [mem_closedBall, dist_zero_right, norm_circleMap_zero,
      abs_of_nonneg hr'.1] using hr'.2
  have hg := hL _ hu _ hv
  have hdiff : circleMap 0 r θ-circleMap 0 r' θ = circleMap 0 (r-r') θ := by
    simp only [circleMap_zero, Complex.ofReal_sub, sub_mul]
  rw [hdiff, norm_circleMap_zero] at hg
  have heq : (c*actualHarmonic F (circleMap 0 r θ)).re-
        (c*actualHarmonic F (circleMap 0 r' θ)).re =
      (c*(actualHarmonic F (circleMap 0 r θ)-actualHarmonic F (circleMap 0 r' θ))).re := by
    simp only [mul_sub, Complex.sub_re]
  rw [heq]
  calc
    |(c*(actualHarmonic F (circleMap 0 r θ)-actualHarmonic F (circleMap 0 r' θ))).re| ≤
        ‖c*(actualHarmonic F (circleMap 0 r θ)-actualHarmonic F (circleMap 0 r' θ))‖ :=
      Complex.abs_re_le_norm _
    _ = ‖c‖*‖actualHarmonic F (circleMap 0 r θ)-actualHarmonic F (circleMap 0 r' θ)‖ :=
      norm_mul _ _
    _ ≤ ‖c‖*(L*|r-r'|) := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = ‖c‖*L*|r-r'| := by ring

end SpringerLean
