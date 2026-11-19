import SpringerLean.Round725RegularInnerTop
import SpringerLean.Round721RegularRadialTrace
import SpringerLean.Round693AngularTopUniform

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Uniform regularization error on EACH fixed inner disk, from the
actual germ's Lipschitz bound.  No boundary values of the original F. -/
theorem regularHarmonic_exists_actual_uniform_error
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s → s < 1 →
      ∀ z ∈ closedBall (0 : ℂ) r,
        ‖regularHarmonic s F z-actualHarmonic F z‖ ≤ 2*M*r*(1-s) := by
  obtain ⟨M, hM0, hM⟩ := exteriorForwardGerm_exists_disk_lipschitz F hc hr0 hr1
  refine ⟨M, hM0, ?_⟩
  intro s hs0 hs1 z hz
  have hz' : ‖z‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hcu : conj z ∈ closedBall (0 : ℂ) r := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hz'
  have hsc : (s : ℂ)*conj z ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_conj,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    exact (mul_le_of_le_one_left (norm_nonneg z) hs1.le).trans hz'
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) r := by simp [hr0]
  have hg0 : ‖exteriorForwardGerm F (conj z)‖ ≤ M*‖z‖ := by
    simpa only [exteriorForwardGerm_zero, sub_zero, Complex.norm_conj] using hM _ hcu 0 hzero
  have hg := hM _ hsc _ hcu
  have hdiff : ‖(s : ℂ)*conj z-conj z‖ = (1-s)*‖z‖ := by
    have heq : (s : ℂ)*conj z-conj z = ((s-1 : ℝ) : ℂ)*conj z := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : s-1 ≤ 0)]
    ring
  rw [hdiff] at hg
  have heq : regularHarmonic s F z-actualHarmonic F z =
      (s : ℂ)*(exteriorForwardGerm F ((s : ℂ)*conj z)-exteriorForwardGerm F (conj z))+
        ((s-1 : ℝ) : ℂ)*exteriorForwardGerm F (conj z) := by
    simp only [regularHarmonic, regularForwardGerm, actualHarmonic]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖(s : ℂ)*(exteriorForwardGerm F ((s : ℂ)*conj z)-exteriorForwardGerm F (conj z))‖+
        ‖((s-1 : ℝ) : ℂ)*exteriorForwardGerm F (conj z)‖ := norm_add_le _ _
    _ = s*‖exteriorForwardGerm F ((s : ℂ)*conj z)-exteriorForwardGerm F (conj z)‖+
        (1-s)*‖exteriorForwardGerm F (conj z)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs0,
        abs_of_nonpos (by linarith : s-1 ≤ 0)]
      ring
    _ ≤ s*(M*((1-s)*‖z‖))+(1-s)*(M*‖z‖) := add_le_add
      (mul_le_mul_of_nonneg_left hg hs0.le)
      (mul_le_mul_of_nonneg_left hg0 (by linarith))
    _ = (s+1)*(M*(1-s)*‖z‖) := by ring
    _ ≤ 2*(M*(1-s)*‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith : s+1 ≤ 2) (by positivity)
    _ ≤ 2*(M*(1-s)*r) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hz' (by positivity : 0 ≤ M*(1-s))) (by norm_num)
    _ = 2*M*r*(1-s) := by ring

/-- Quantitative stability of the SAME actual top function under s->1.
This genuinely proves a uniform angular error, not just pointwise
convergence of a selected family of maximizing sets. -/
theorem actualAngularTopValue_exists_regularization_error
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, 0 < s → s < 1 →
      ∀ (c : ℂ) (h : ℝ), 0 < h → h < Real.pi →
        |actualAngularTopValue (rescaleExterior s F) c r h-
          actualAngularTopValue F c r h| ≤ 4*h*‖c‖*M*r*(1-s) := by
  obtain ⟨M, hM0, hM⟩ := regularHarmonic_exists_actual_uniform_error F hc hr0 hr1
  refine ⟨M, hM0, ?_⟩
  intro s hs0 hs1 c h hh0 hhpi
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hdiff (θ : ℝ) (_ : θ ∈ Ioc 0 (2*Real.pi)) :
      |(c*actualHarmonic (rescaleExterior s F) (circleMap 0 r θ)).re-
        (c*actualHarmonic F (circleMap 0 r θ)).re| ≤ ‖c‖*(2*M*r*(1-s)) := by
    have hz : circleMap 0 r θ ∈ closedBall (0 : ℂ) r := by
      simp only [mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr0, le_refl]
    have hg := hM s hs0 hs1 _ hz
    rw [← actualHarmonic_rescale_eq_regular s hs0 F] at hg
    have heq : (c*actualHarmonic (rescaleExterior s F) (circleMap 0 r θ)).re-
        (c*actualHarmonic F (circleMap 0 r θ)).re =
        (c*(actualHarmonic (rescaleExterior s F) (circleMap 0 r θ)-
          actualHarmonic F (circleMap 0 r θ))).re := by
      simp only [mul_sub, Complex.sub_re]
    rw [heq]
    exact (Complex.abs_re_le_norm _).trans (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hg (norm_nonneg _))
  have hv := actualAngularTopValue_abs_sub_le_uniform (rescaleExterior s F) F hcG hc c c
    hr0 hr1 hr0 hr1 hh0 hhpi (‖c‖*(2*M*r*(1-s))) hdiff
  convert hv using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.regularHarmonic_exists_actual_uniform_error
#print axioms SpringerLean.actualAngularTopValue_exists_regularization_error
