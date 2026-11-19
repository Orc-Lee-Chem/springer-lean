import SpringerLean.Round30AnglePair
import SpringerLean.Round28AuxClosed

open MeasureTheory Set Metric

namespace SpringerLean

private theorem verticalCircle_re (a h ρ θ : ℝ) :
    (circleMap ((a : ℂ) + (h : ℂ) * Complex.I) ρ θ).re =
      a + ρ * Real.cos θ := by
  rw [show circleMap ((a : ℂ) + (h : ℂ) * Complex.I) ρ θ =
    ((a : ℂ) + (h : ℂ) * Complex.I) + circleMap 0 ρ θ from by simp [circleMap]]
  simp [Complex.add_re, circleMap_zero_re]

private theorem verticalCircle_im (a h ρ θ : ℝ) :
    (circleMap ((a : ℂ) + (h : ℂ) * Complex.I) ρ θ).im =
      h + ρ * Real.sin θ := by
  rw [show circleMap ((a : ℂ) + (h : ℂ) * Complex.I) ρ θ =
    ((a : ℂ) + (h : ℂ) * Complex.I) + circleMap 0 ρ θ from by simp [circleMap]]
  simp [Complex.add_im, circleMap_zero_im]

/-- The actual auxiliary on a circle lying strictly above the real axis has
an exact upper/lower semicircle pairing in its original (a,h) coordinates. -/
theorem regularVerticalAuxiliary_circleAverage_eq_angle_pair
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρh : ρ < h) :
    Real.circleAverage
      (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
      ((a : ℂ) + (h : ℂ) * Complex.I) ρ =
      (2 * Real.pi)⁻¹ *
        ∫ θ in (0:ℝ)..Real.pi,
          (regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
           regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h - ρ * Real.sin θ)) := by
  let c : ℂ := (a : ℂ) + (h : ℂ) * Complex.I
  let f : ℝ → ℝ := fun θ => regularVerticalAuxiliary F s ξ
    (circleMap c ρ θ).re (circleMap c ρ θ).im
  have hcircle (θ : ℝ) : 0 ≤ (circleMap c ρ θ).im := by
    rw [show c = ((a : ℂ) + (h : ℂ) * Complex.I) from rfl,
      verticalCircle_im]
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hbound : -1 ≤ Real.sin θ := (abs_le.mp hs).1
    nlinarith
  have hcont : Continuous f :=
    (regularVerticalAuxiliary_continuousOn_upperHalfPlane
      F hc hs0 hs1 ξ hξ).comp_continuous
        (by fun_prop : Continuous (fun θ : ℝ =>
          ((circleMap c ρ θ).re, (circleMap c ρ θ).im)))
        (fun θ => hcircle θ)
  have hint : IntervalIntegrable f volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hper : Function.Periodic f (2 * Real.pi) := by
    intro θ
    simp [f, periodic_circleMap c ρ θ]
  have hpair := periodic_angle_integral_pair f hper hint
  rw [Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2 * Real.pi, f θ) = _
  rw [hpair]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp [f, c]
  rw [verticalCircle_re, verticalCircle_im,
    verticalCircle_re, verticalCircle_im]
  simpa only [Real.cos_neg, Real.sin_neg, mul_neg, sub_eq_add_neg]

end SpringerLean
