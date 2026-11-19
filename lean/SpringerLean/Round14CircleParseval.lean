import SpringerLean.Round14QuadraticPrelude
import SpringerLean.CircleFinite
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open MeasureTheory AddCircle

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- The positive-frequency Fourier polynomial associated with a finite
Taylor truncation on the circle of radius `r`. -/
noncomputable def analyticCirclePartial (d : ℕ → ℂ) (r : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) : ℂ :=
  finiteFourierFamily (2 * Real.pi) (Finset.range M)
    (fun j : ℕ => (j : ℤ))
    (fun j => d j * (r : ℂ) ^ j) θ

private theorem fourier_natCast_eq_circleMap_pow (j : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (j : ℤ)
      (θ : AddCircle (2 * Real.pi)) = (circleMap 0 1 θ) ^ j := by
  rw [fourier_coe_apply, circleMap_zero]
  simp only [Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  push_cast
  ring

/-- Evaluation of a finite Taylor polynomial on an actual radius-`r`
complex circle matches its positive-frequency Fourier polynomial. -/
theorem analyticCirclePartial_coe_eq
    (d : ℕ → ℂ) (r : ℝ) (M : ℕ) (θ : ℝ) :
    analyticCirclePartial d r M (θ : AddCircle (2 * Real.pi)) =
      ∑ j ∈ Finset.range M, d j * (circleMap 0 r θ) ^ j := by
  unfold analyticCirclePartial finiteFourierFamily
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourier_natCast_eq_circleMap_pow, circleMap_zero, circleMap_zero]
  simp [mul_pow]
  ring

/-- Finite normalized Haar Parseval for the same Taylor truncation. -/
theorem analyticCirclePartial_energy
    (d : ℕ → ℂ) (r : ℝ) (M : ℕ) :
    (∫ θ : AddCircle (2 * Real.pi),
      ‖analyticCirclePartial d r M θ‖ ^ 2 ∂haarAddCircle) =
      ∑ j ∈ Finset.range M, ‖d j * (r : ℂ) ^ j‖ ^ 2 := by
  have h := finiteFourierFamily_energy (2 * Real.pi)
    (Finset.range M) (fun j : ℕ => (j : ℤ))
    (fun j => d j * (r : ℂ) ^ j) (by exact_mod_cast (Int.ofNat_injective : Function.Injective (fun j : ℕ => (j : ℤ))))
  exact h

/-- Exact finite Taylor Parseval with the same `Real.circleAverage`
normalization used by the inner-circle convex-order problem. -/
theorem finiteTaylor_circleAverage_energy
    (d : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) (M : ℕ) :
    Real.circleAverage
      (fun z : ℂ => ‖∑ j ∈ Finset.range M, d j * z ^ j‖ ^ 2)
      0 r =
      ∑ j ∈ Finset.range M, ‖d j‖ ^ 2 * r ^ (2 * j) := by
  let P : AddCircle (2 * Real.pi) → ℝ :=
    fun θ => ‖analyticCirclePartial d r M θ‖ ^ 2
  have hinterval :
      (∫ θ in 0..2 * Real.pi, P (θ : AddCircle (2 * Real.pi))) =
      ∫ θ : AddCircle (2 * Real.pi), P θ := by
    simpa only [zero_add] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 P)
  have hhaar :
      (∫ θ : AddCircle (2 * Real.pi), P θ ∂haarAddCircle) =
      (2 * Real.pi)⁻¹ * (∫ θ : AddCircle (2 * Real.pi), P θ) := by
    simpa only [smul_eq_mul] using
      (AddCircle.integral_haarAddCircle (T := 2 * Real.pi) (f := P))
  calc
    Real.circleAverage
        (fun z : ℂ => ‖∑ j ∈ Finset.range M, d j * z ^ j‖ ^ 2)
        0 r = ∫ θ : AddCircle (2 * Real.pi), P θ ∂haarAddCircle := by
          unfold Real.circleAverage
          simp only [zero_add, smul_eq_mul]
          rw [hhaar, ← hinterval]
          congr 1
          apply intervalIntegral.integral_congr
          intro θ hθ
          exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (analyticCirclePartial_coe_eq d r M θ).symm
    _ = ∑ j ∈ Finset.range M, ‖d j * (r : ℂ) ^ j‖ ^ 2 :=
      analyticCirclePartial_energy d r M
    _ = ∑ j ∈ Finset.range M, ‖d j‖ ^ 2 * r ^ (2 * j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
      ring


/-- The normalized angular average and normalized Haar integral are the
same for a function sampled on the actual circle of radius `r`. -/
theorem circleAverage_eq_haar_circle (h : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage h 0 r =
      ∫ θ : AddCircle (2 * Real.pi), h (exteriorCirclePoint r θ)
        ∂haarAddCircle := by
  have hpoint (θ : ℝ) :
      exteriorCirclePoint r (θ : AddCircle (2 * Real.pi)) =
        circleMap 0 r θ := by
    unfold exteriorCirclePoint
    rw [fourier_coe_apply, circleMap_zero]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hinterval :
      (∫ θ in 0..2 * Real.pi,
        h (exteriorCirclePoint r (θ : AddCircle (2 * Real.pi)))) =
      ∫ θ : AddCircle (2 * Real.pi), h (exteriorCirclePoint r θ) := by
    simpa only [zero_add] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
        (fun θ : AddCircle (2 * Real.pi) => h (exteriorCirclePoint r θ)))
  have hhaar := AddCircle.integral_haarAddCircle
    (T := 2 * Real.pi)
    (f := fun θ : AddCircle (2 * Real.pi) => h (exteriorCirclePoint r θ))
  unfold Real.circleAverage
  simp only [smul_eq_mul]
  rw [← hinterval] at hhaar
  simpa only [hpoint, smul_eq_mul] using hhaar.symm

/-- The same angular-to-Haar identity for complex-valued circle data. -/
theorem circleAverage_eq_haar_circle_complex (h : ℂ → ℂ) (r : ℝ) :
    Real.circleAverage h 0 r =
      ∫ θ : AddCircle (2 * Real.pi), h (exteriorCirclePoint r θ)
        ∂haarAddCircle := by
  have hpoint (θ : ℝ) :
      exteriorCirclePoint r (θ : AddCircle (2 * Real.pi)) =
        circleMap 0 r θ := by
    unfold exteriorCirclePoint
    rw [fourier_coe_apply, circleMap_zero]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  have hinterval :
      (∫ θ in 0..2 * Real.pi,
        h (exteriorCirclePoint r (θ : AddCircle (2 * Real.pi)))) =
      ∫ θ : AddCircle (2 * Real.pi), h (exteriorCirclePoint r θ) := by
    simpa only [zero_add] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
        (fun θ : AddCircle (2 * Real.pi) => h (exteriorCirclePoint r θ)))
  have hhaar := AddCircle.integral_haarAddCircle
    (T := 2 * Real.pi)
    (f := fun θ : AddCircle (2 * Real.pi) => h (exteriorCirclePoint r θ))
  unfold Real.circleAverage
  rw [← hinterval] at hhaar
  simpa only [hpoint] using hhaar.symm
end SpringerLean
