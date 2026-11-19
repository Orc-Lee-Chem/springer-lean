import SpringerLean.AnnulusMax

open Complex
open scoped ComplexConjugate

namespace SpringerLean

/-- The value-space real-linear correction, packaged as a map for determinant
and area-scaling theorems. -/
noncomputable def exteriorLinearCorrectionRealMap
    (F : ℂ → ℂ) (R : ℝ) : ℂ →ₗ[ℝ] ℂ :=
  (1 : ℂ →ₗ[ℝ] ℂ) -
    ((exteriorForwardCoeff F 1 / (R : ℂ) ^ 2) • (1 : ℂ →ₗ[ℝ] ℂ)).comp
      Complex.conjAe.toLinearMap

@[simp] theorem exteriorLinearCorrectionRealMap_apply
    (F : ℂ → ℂ) (R : ℝ) (w : ℂ) :
    exteriorLinearCorrectionRealMap F R w =
      exteriorLinearCorrection F R w := by
  simp [exteriorLinearCorrectionRealMap, exteriorLinearCorrection]

/-- Determinant of `w ↦ w-c conj(w)`, with `c=b₁/R²`. -/
theorem exteriorLinearCorrectionRealMap_det
    (F : ℂ → ℂ) (R : ℝ) :
    (exteriorLinearCorrectionRealMap F R).det =
      1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2 := by
  let c : ℂ := exteriorForwardCoeff F 1 / (R : ℂ) ^ 2
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have hm : (exteriorLinearCorrectionRealMap F R).toMatrix
      Complex.basisOneI Complex.basisOneI =
      !![1 - c.re, -c.im; -c.im, 1 + c.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, exteriorLinearCorrectionRealMap_apply,
        exteriorLinearCorrection, c, Complex.mul_re, Complex.mul_im]
  rw [hm, Matrix.det_fin_two_of]
  calc
    (1 - c.re) * (1 + c.re) - -c.im * -c.im =
        1 - (c.re ^ 2 + c.im ^ 2) := by ring
    _ = 1 - ‖c‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring

/-- The correction preserves orientation once the outer radius dominates
the first Laurent coefficient. -/
theorem exteriorLinearCorrectionRealMap_det_pos
    (F : ℂ → ℂ) {R : ℝ}
    (hR : max 2 (‖exteriorForwardCoeff F 1‖ + 2) ≤ R) :
    0 < (exteriorLinearCorrectionRealMap F R).det := by
  rw [exteriorLinearCorrectionRealMap_det]
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hRbig : ‖exteriorForwardCoeff F 1‖ + 2 ≤ R :=
    le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := by linarith
  have hRsq : 0 < R ^ 2 := by positivity
  have hB : 0 ≤ ‖exteriorForwardCoeff F 1‖ := norm_nonneg _
  have hBlt : ‖exteriorForwardCoeff F 1‖ < R ^ 2 := by nlinarith
  have hratio :
      ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ =
        ‖exteriorForwardCoeff F 1‖ / R ^ 2 := by
    rw [norm_div, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hRpos]
  rw [hratio]
  have hlt : ‖exteriorForwardCoeff F 1‖ / R ^ 2 < 1 :=
    (div_lt_iff₀ hRsq).mpr (by simpa using hBlt)
  have hnonneg : 0 ≤ ‖exteriorForwardCoeff F 1‖ / R ^ 2 :=
    div_nonneg hB hRsq.le
  nlinarith

/-- Volume scaling for the actual corrected image of any measurable set. -/
theorem exteriorLinearCorrection_image_area
    (F : ℂ → ℂ) (R : ℝ) (s : Set ℂ) :
    MeasureTheory.volume
      (exteriorLinearCorrection F R '' s) =
        ENNReal.ofReal
          |1 - ‖exteriorForwardCoeff F 1 / (R : ℂ) ^ 2‖ ^ 2| *
          MeasureTheory.volume s := by
  have h := MeasureTheory.Measure.addHaar_image_linearMap
    MeasureTheory.volume (exteriorLinearCorrectionRealMap F R) s
  simpa only [exteriorLinearCorrectionRealMap_apply,
    exteriorLinearCorrectionRealMap_det] using h

end SpringerLean
