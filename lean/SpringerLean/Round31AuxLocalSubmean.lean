import SpringerLean.Round31FiniteComplementPair
import SpringerLean.Round30AuxAnglePair
import SpringerLean.Round28AuxClosed

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual vertical auxiliary satisfies local circle submean at every
strictly positive height, with no optimizer or tail hypotheses in the type. -/
theorem regularVerticalAuxiliary_local_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      regularVerticalAuxiliary F s ξ a h ≤
        Real.circleAverage
          (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
          ((a : ℂ) + (h : ℂ) * Complex.I) ρ := by
  obtain ⟨E, hE, T, hT, hES, hmin, δ, hδ, hpair⟩ :=
    regularVerticalAuxiliary_semicircle_finite_complement_lower
      F hc hs0 hs1 ξ hξ a h hh
  refine ⟨min δ h, lt_min hδ hh, ?_⟩
  intro ρ hρ hρmin
  have hρδ : ρ < δ := lt_of_lt_of_le hρmin (min_le_left _ _)
  have hρh : ρ < h := lt_of_lt_of_le hρmin (min_le_right _ _)
  have hcenter := regularVerticalAuxiliary_eq_finiteComplement_of_minimizer
    F hc hs0 hs1 ξ hξ a h T hh E hE hmin hT hES
  have hfinite := regularVerticalFiniteComplement_circle_submean
    F hc hs0 hs1 ξ hξ E hE.1 hE.2.1 a h T ρ hh hT hES hρ hρh
  have hfinitepair := regularVerticalFiniteComplement_circleAverage_eq_angle_pair
    F hc hs0 hs1 ξ hξ E hE.1 a h T ρ hh hT hρ hρh
  have hUpair := regularVerticalAuxiliary_circleAverage_eq_angle_pair
    F hc hs0 hs1 ξ hξ a h ρ hρ.le hρh
  let q : ℂ → ℝ := fun z =>
    regularVerticalFiniteComplement F s ξ z.re h T z.im E
  have hci : CircleIntegrable q (a : ℂ) ρ :=
    regularVerticalFiniteComplement_circleIntegrable
      F hc hs0 hs1 ξ hξ E hE.1 a h T ρ hh hT hρ hρh
  have hre (φ : ℝ) : (circleMap (a : ℂ) ρ φ).re = a + ρ * Real.cos φ := by
    rw [show circleMap (a : ℂ) ρ φ = (a : ℂ) + circleMap 0 ρ φ from by
      simp [circleMap]]
    simp [Complex.add_re, circleMap_zero_re]
  have him (φ : ℝ) : (circleMap (a : ℂ) ρ φ).im = ρ * Real.sin φ := by
    rw [show circleMap (a : ℂ) ρ φ = (a : ℂ) + circleMap 0 ρ φ from by
      simp [circleMap]]
    simp [Complex.add_im, circleMap_zero_im]
  have hFfun : (fun θ : ℝ =>
      regularVerticalFiniteComplement F s ξ
        (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E +
      regularVerticalFiniteComplement F s ξ
        (a + ρ * Real.cos θ) h T (-(ρ * Real.sin θ)) E) =
      (fun θ => q (circleMap (a : ℂ) ρ θ) +
        q (circleMap (a : ℂ) ρ (-θ))) := by
    funext θ
    dsimp [q]
    rw [hre θ, him θ, hre (-θ), him (-θ)]
    simp only [Real.cos_neg, Real.sin_neg, mul_neg]
  have hFint : IntervalIntegrable (fun θ : ℝ =>
      regularVerticalFiniteComplement F s ξ
        (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E +
      regularVerticalFiniteComplement F s ξ
        (a + ρ * Real.cos θ) h T (-(ρ * Real.sin θ)) E)
      volume 0 Real.pi := by
    rw [hFfun]
    exact circleIntegrable_angle_pair q a ρ hci
  have hUpos (θ : ℝ) : 0 ≤ h + ρ * Real.sin θ := by
    have hs := Real.abs_sin_le_one θ
    have hb := (abs_le.mp hs).1
    nlinarith
  have hUneg (θ : ℝ) : 0 ≤ h - ρ * Real.sin θ := by
    have hs := Real.abs_sin_le_one θ
    have hb := (abs_le.mp hs).2
    nlinarith
  have hUplus : Continuous (fun θ : ℝ =>
      regularVerticalAuxiliary F s ξ
        (a + ρ * Real.cos θ) (h + ρ * Real.sin θ)) :=
    (regularVerticalAuxiliary_continuousOn_upperHalfPlane
      F hc hs0 hs1 ξ hξ).comp_continuous
        (by fun_prop : Continuous (fun θ : ℝ =>
          (a + ρ * Real.cos θ, h + ρ * Real.sin θ)))
        (fun θ => hUpos θ)
  have hUminus : Continuous (fun θ : ℝ =>
      regularVerticalAuxiliary F s ξ
        (a + ρ * Real.cos θ) (h - ρ * Real.sin θ)) :=
    (regularVerticalAuxiliary_continuousOn_upperHalfPlane
      F hc hs0 hs1 ξ hξ).comp_continuous
        (by fun_prop : Continuous (fun θ : ℝ =>
          (a + ρ * Real.cos θ, h - ρ * Real.sin θ)))
        (fun θ => hUneg θ)
  have hUint : IntervalIntegrable (fun θ : ℝ =>
      regularVerticalAuxiliary F s ξ
        (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
      regularVerticalAuxiliary F s ξ
        (a + ρ * Real.cos θ) (h - ρ * Real.sin θ))
      volume 0 Real.pi :=
    (hUplus.add hUminus).intervalIntegrable _ _
  have hmono :
      (∫ θ in (0:ℝ)..Real.pi,
        (regularVerticalFiniteComplement F s ξ
          (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E +
         regularVerticalFiniteComplement F s ξ
          (a + ρ * Real.cos θ) h T (-(ρ * Real.sin θ)) E)) ≤
      (∫ θ in (0:ℝ)..Real.pi,
        (regularVerticalAuxiliary F s ξ
          (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
         regularVerticalAuxiliary F s ξ
          (a + ρ * Real.cos θ) (h - ρ * Real.sin θ))) := by
    apply intervalIntegral.integral_mono_on Real.pi_pos.le hFint hUint
    intro θ hθ
    have hp := hpair ρ hρ.le hρδ θ hθ
    linarith
  calc
    regularVerticalAuxiliary F s ξ a h =
        regularVerticalFiniteComplement F s ξ a h T 0 E := hcenter
    _ ≤ Real.circleAverage
          (fun z : ℂ => regularVerticalFiniteComplement F s ξ z.re h T z.im E)
          (a : ℂ) ρ := hfinite
    _ = (2 * Real.pi)⁻¹ *
        (∫ θ in (0:ℝ)..Real.pi,
          (regularVerticalFiniteComplement F s ξ
            (a + ρ * Real.cos θ) h T (ρ * Real.sin θ) E +
           regularVerticalFiniteComplement F s ξ
            (a + ρ * Real.cos θ) h T (-(ρ * Real.sin θ)) E)) := hfinitepair
    _ ≤ (2 * Real.pi)⁻¹ *
        (∫ θ in (0:ℝ)..Real.pi,
          (regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h + ρ * Real.sin θ) +
           regularVerticalAuxiliary F s ξ
            (a + ρ * Real.cos θ) (h - ρ * Real.sin θ))) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Real.circleAverage
          (fun z : ℂ => regularVerticalAuxiliary F s ξ z.re z.im)
          ((a : ℂ) + (h : ℂ) * Complex.I) ρ := hUpair.symm

end SpringerLean