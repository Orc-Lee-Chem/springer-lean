import SpringerLean.Round1655RadialPhaseDerivativeBound

open scoped ComplexConjugate

namespace SpringerLean

/-- A signed mixed term is paid by the absolute-value coefficient
without assuming a sign for either the coefficient or the field. -/
theorem signed_cross_cost_le
    {K C x v p : ℝ} (hK : 0 ≤ K)
    (hx : |x| ≤ v*p) :
    K*C*x ≤ K*|C| * v*p := by
  have hcoef := mul_le_mul_of_nonneg_left hx (abs_nonneg C)
  have hcross : C*x ≤ |C| * (v*p) := by
    calc
      C*x ≤ |C*x| := le_abs_self _
      _ = |C| * |x| := abs_mul _ _
      _ ≤ |C| * (v*p) := hcoef
  have hh := mul_le_mul_of_nonneg_left hcross hK
  nlinarith

/-- Actual inverse-field drift costs the printed absolute-value
coefficient times the normalized phase and gradient lengths. -/
theorem actualHarmonicPhase_drift_cross_cost_le
    (F : ℂ → ℂ) (k : ℕ) (beta : ℂ) (z : ℂ)
    (C : ℝ) :
    let U := actualHarmonicPhaseField F k beta
    let Q := (conj (actualHarmonic F z))⁻¹
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    (k:ℝ)*C*(U z*(Q.re*ux+Q.im*uy)) ≤
      (k:ℝ)*|C| * |U z/‖actualHarmonic F z‖| *
        Real.sqrt (ux^2+uy^2) := by
  let U := actualHarmonicPhaseField F k beta
  let Q := (conj (actualHarmonic F z))⁻¹
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  exact signed_cross_cost_le (Nat.cast_nonneg k)
    (inverseConjugate_drift_abs_le (actualHarmonic F z) (U z) ux uy)

/-- Actual radial phase derivative costs the same gradient length. -/
theorem actualHarmonicPhase_radial_cross_cost_le
    (F : ℂ → ℂ) (k : ℕ) (beta : ℂ)
    {z : ℂ} (hz0 : z ≠ 0) (C : ℝ) :
    let U := actualHarmonicPhaseField F k beta
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let u := U z/‖actualHarmonic F z‖
    (k:ℝ)*C*u*((fderiv ℝ U z) (z/‖z‖)) ≤
      (k:ℝ)*|C| * |u| * Real.sqrt (ux^2+uy^2) := by
  let U := actualHarmonicPhaseField F k beta
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let u := U z/‖actualHarmonic F z‖
  have hr := phase_radial_derivative_abs_le U hz0
  have hx : |u*((fderiv ℝ U z) (z/‖z‖))| ≤
      |u| * Real.sqrt (ux^2+uy^2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  have h := signed_cross_cost_le (K := (k:ℝ)) (C := C)
    (x := u*((fderiv ℝ U z) (z/‖z‖)))
    (v := |u|) (p := Real.sqrt (ux^2+uy^2))
    (Nat.cast_nonneg k) hx
  convert h using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.signed_cross_cost_le
#print axioms SpringerLean.actualHarmonicPhase_drift_cross_cost_le
#print axioms SpringerLean.actualHarmonicPhase_radial_cross_cost_le
