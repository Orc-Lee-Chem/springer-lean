import SpringerLean.Round1641InverseConjugateDrift

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual drift PDE in the exact form needed after multiplying
the P flux by U and pairing it with the S flux. This is valid away
from H=0; the underlying no-division PDE remains valid at H=0. -/
theorem actualHarmonicPhase_drift_PDE_divided
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let Q := (conj (actualHarmonic F z))⁻¹
    U z * actualHarmonicPhaseLaplacian F k beta z =
      4*((k:ℝ)-1)*U z *
        (Q.re*(fderiv ℝ U z) (1:ℂ) +
         Q.im*(fderiv ℝ U z) Complex.I) -
      4*(k:ℝ)*((k:ℝ)-1)*
        (U z/‖actualHarmonic F z‖)^2 := by
  let U := actualHarmonicPhaseField F k beta
  let H := actualHarmonic F z
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  have hpde := actualHarmonicPhase_drift_PDE_norm
    F hc k hk beta hz
  have hdot := inverseConjugate_dot_gradient H ux uy
  have hy : (‖H‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr hH
  have hmul := congrArg (fun x : ℝ => U z*x) hpde
  dsimp only [U, H, ux, uy] at hdot hmul ⊢
  rw [hdot]
  field_simp [hy]
  nlinarith [hmul]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_drift_PDE_divided
