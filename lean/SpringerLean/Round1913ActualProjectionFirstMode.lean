import SpringerLean.Round1912ProjectionTraceSquare
import SpringerLean.Round14Quadratic

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace SpringerLean

private theorem actualHarmonic_projection_circle_first_mode
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (c : ℂ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 * r ^ 2 / 8 ≤
      Real.circleAverage
        (fun z : ℂ => ((c * actualHarmonic F z).re / 2) ^ 2) 0 r := by
  let J := projectionAnalytic F c
  have hsub : sphere (0 : ℂ) |r| ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hzNorm : ‖z‖ = r := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
    simpa [mem_ball, dist_zero_right, hzNorm] using hr1
  have hcont : ContinuousOn J (sphere (0 : ℂ) |r|) :=
    (projectionAnalytic_analyticOnNhd F hc c).continuousOn.mono hsub
  have hhalf := real_square_circleAverage_eq_half_energy J r hcont
    (projectionAnalytic_sq_circleAverage_zero F hc c hr0.le hr1)
  have hfirst := projectionAnalytic_circle_energy_first_mode F hc c hr0 hr1
  have hreflection :
      Real.circleAverage
        (fun z : ℂ => (c * actualHarmonic F z).re ^ 2) 0 r =
      Real.circleAverage (fun z : ℂ => (J z).re ^ 2) 0 r := by
    rw [← circleAverage_comp_conj_zero
      (fun z : ℂ => (c * actualHarmonic F z).re ^ 2) r]
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact congrArg (fun x : ℝ => x ^ 2)
      (actualHarmonic_projection_reflection F c z)
  have hscale :
      Real.circleAverage
        (fun z : ℂ => ((c * actualHarmonic F z).re / 2) ^ 2) 0 r =
      (1 / 4 : ℝ) * Real.circleAverage
        (fun z : ℂ => (c * actualHarmonic F z).re ^ 2) 0 r := by
    have hpoint (z : ℂ) :
        ((c * actualHarmonic F z).re / 2) ^ 2 =
          (1 / 4 : ℝ) • (c * actualHarmonic F z).re ^ 2 := by
      simp only [smul_eq_mul]
      ring
    simp_rw [hpoint]
    simpa only [smul_eq_mul] using
      (Real.circleAverage_fun_smul (a := (1 / 4 : ℝ))
        (f := fun z : ℂ => (c * actualHarmonic F z).re ^ 2)
        (c := (0 : ℂ)) (R := r))
  rw [hscale, hreflection]
  linarith

/-- The first Fourier mode gives the quantitative second-moment lower
bound on the original map's actual radial boundary trace. -/
theorem actualBoundaryProjectionSecondMoment_first_mode
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (c : ℂ) (hcunit : ‖c‖ = 1) :
    ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 / 8 ≤
      actualBoundaryProjectionSecondMoment F c := by
  have hleft : Tendsto
      (fun r : ℝ =>
        ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 * r ^ 2 / 8)
      (𝓝[<] (1 : ℝ))
      (𝓝 (‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 / 8)) := by
    have hcont : Continuous (fun r : ℝ =>
        ‖conj c + c * exteriorForwardCoeff F 1‖ ^ 2 * r ^ 2 / 8) := by
      fun_prop
    simpa only [one_pow, mul_one] using
      hcont.continuousAt.tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hright := actualHarmonic_projection_square_tendsto_trace F hc c hcunit
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact actualHarmonic_projection_circle_first_mode F hc c hr.1 hr.2

/-- This is the missing first-mode input for the [4,8] interpolation,
with the phase chosen from the first forward Laurent coefficient. -/
theorem actualBoundaryProjectionSecondMoment_phase_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (1 + ‖exteriorForwardCoeff F 1‖) ^ 2 / 8 ≤
        actualBoundaryProjectionSecondMoment F c := by
  obtain ⟨c, hcunit, heq⟩ :=
    projection_first_mode_phase_max (exteriorForwardCoeff F 1)
  refine ⟨c, hcunit, ?_⟩
  rw [← heq]
  exact actualBoundaryProjectionSecondMoment_first_mode F hc c hcunit

end SpringerLean

#print axioms SpringerLean.actualBoundaryProjectionSecondMoment_phase_bound
