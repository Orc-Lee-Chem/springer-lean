import SpringerLean.Round1861ActualTraceIntegrability

open MeasureTheory Filter
open scoped Topology

namespace SpringerLean

theorem rescaleExterior_circle_real_moment_eq
    (F : ℂ → ℂ) (s : ℝ) (hs : 0 ≤ s) (p : ℝ) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ p) 0 1 =
      s ^ p * Real.circleAverage (fun ζ : ℂ => ‖F ζ‖ ^ p) 0 s⁻¹ := by
  have hfun (ζ : ℂ) : ‖rescaleExterior s F ζ‖ ^ p =
      s ^ p * ‖F ((s⁻¹ : ℝ) * ζ)‖ ^ p := by
    rw [rescaleExterior, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs, Real.mul_rpow hs (norm_nonneg _)]
    congr 2
    push_cast
    rw [div_eq_mul_inv, mul_comm]
  calc
    _ = Real.circleAverage (fun ζ : ℂ => s ^ p * ‖F ((s⁻¹ : ℝ) * ζ)‖ ^ p) 0 1 := by
      congr 1
      funext ζ
      exact hfun ζ
    _ = s ^ p * Real.circleAverage (fun ζ : ℂ => ‖F ((s⁻¹ : ℝ) * ζ)‖ ^ p) 0 1 := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (f := fun ζ : ℂ => ‖F ((s⁻¹ : ℝ) * ζ)‖ ^ p)
          (a := s ^ p) (c := 0) (R := 1))
    _ = _ := by
      have hh := Real.circleAverage_eq_circleAverage_zero_one
        (f := fun ζ : ℂ => ‖F ζ‖ ^ p) (c := 0) (R := s⁻¹)
      simpa only [add_zero] using congrArg (fun x : ℝ => s ^ p * x) hh.symm

/-- The actual analytic regularizations converge to the original map's
boundary moment for every nonnegative real exponent. -/
theorem actualBoundaryRadialMoment_rescale_circle_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto
      (fun s : ℝ => Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ p) 0 1)
      (𝓝[<] (1 : ℝ)) (𝓝 (actualBoundaryRadialMoment F p)) := by
  have hpow : Tendsto (fun s : ℝ => s ^ p) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Real.one_rpow] using (Real.continuous_rpow_const hp).continuousAt.tendsto.mono_left
      (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hh := hpow.mul (actualBoundaryRadialMoment_circle_tendsto F hc p hp)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
  exact (rescaleExterior_circle_real_moment_eq F s hs.1.le p).symm

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_rescale_circle_tendsto
