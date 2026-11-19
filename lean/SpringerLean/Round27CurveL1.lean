import SpringerLean.Round27PointKernelL1

open MeasureTheory Set

namespace SpringerLean

/-- The angle average of a compensated logarithmic kernel is L1-Lipschitz
in the horizontal line coordinate. -/
theorem verticalCurveKernel_L1_lipschitz_horizontal
    (a a' : ℝ) (W : ℝ → ℂ) (hW : Continuous W) :
    (∫ y : ℝ, |(∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a' (W θ) y)|) ≤
      (2 * Real.pi) * (Real.pi * |a - a'|) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have hA := verticalCurveKernel_integrable a W hW
  have hB := verticalCurveKernel_integrable a' W hW
  have hD : Integrable (fun p : ℝ × ℝ =>
      verticalPointKernel a (W p.1) p.2 -
      verticalPointKernel a' (W p.1) p.2) (μ.prod volume) :=
    hA.sub hB
  have hDN := hD.abs
  have hAi := hA.integral_prod_right
  have hBi := hB.integral_prod_right
  have hDi := hD.integral_prod_right
  have hDNi := hDN.integral_prod_right
  have hae := hA.prod_left_ae
  have hbe := hB.prod_left_ae
  have hpoint : ∀ᵐ y : ℝ ∂volume,
      |(∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a' (W θ) y)| ≤
      ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        |verticalPointKernel a (W θ) y -
          verticalPointKernel a' (W θ) y| := by
    filter_upwards [hae, hbe] with y hay hby
    rw [← integral_sub hay hby]
    exact abs_integral_le_integral_abs
  have hleft : Integrable (fun y : ℝ =>
      |(∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a (W θ) y) -
        (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a' (W θ) y)|) :=
    (hAi.sub hBi).abs
  calc
    (∫ y : ℝ, |(∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a' (W θ) y)|) ≤
      ∫ y : ℝ, ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        |verticalPointKernel a (W θ) y -
          verticalPointKernel a' (W θ) y| :=
      integral_mono_ae hleft hDNi hpoint
    _ = ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        ∫ y : ℝ, |verticalPointKernel a (W θ) y -
          verticalPointKernel a' (W θ) y| := by
      exact (integral_integral_swap
        (f := fun θ y : ℝ => |verticalPointKernel a (W θ) y -
          verticalPointKernel a' (W θ) y|)
        (μ := μ) (ν := volume) hDN).symm
    _ ≤ ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        Real.pi * |a - a'| := by
      apply integral_mono_ae hDN.integral_prod_left (integrable_const _)
      filter_upwards with θ
      exact verticalPointKernel_L1_lipschitz_horizontal a a' (W θ)
    _ = (2 * Real.pi) * (Real.pi * |a - a'|) := by
      simp [MeasureTheory.integral_const, Real.volume_Ioc, Real.pi_nonneg]

end SpringerLean