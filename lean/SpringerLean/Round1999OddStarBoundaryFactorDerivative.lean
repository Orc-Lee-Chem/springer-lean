import SpringerLean.Round1998OddStarTipRadiusDerivative
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace SpringerLean

/-- Algebraically stable form of the moving boundary factor in the
odd-star perturbation. -/
noncomputable def oddStarBoundaryFactor (ζ : ℂ) (t : ℝ) : ℂ :=
  let α : ℂ := (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I
  α ^ 2 * ζ / (α * ζ - (t : ℂ) * Complex.I)

/-- Exact complex first variation of the boundary factor at the
regular star. -/
theorem oddStarBoundaryFactor_hasDerivAt_zero
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    HasDerivAt (oddStarBoundaryFactor ζ)
      (Complex.I * (ζ⁻¹ - 1)) 0 := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - t ^ 2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).pow 2) using 1 <;>
        norm_num <;> (funext t; rfl)
  have hsqrt : HasDerivAt Real.sqrt (1 / 2) (1 : ℝ) := by
    simpa using Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) ≠ 0)
  have hroot : HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) 0 0 := by
    have hsqrt0 : HasDerivAt Real.sqrt (1 / 2) (1 - (0 : ℝ) ^ 2) := by
      simpa using hsqrt
    convert hsqrt0.comp 0 hbase using 1 <;>
      norm_num <;> (funext t; rfl)
  have hcoe : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    have h : HasDerivAt (Complex.ofRealCLM : ℝ → ℂ) 1 0 := by
      simpa using (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasDerivAt
    convert h using 1
    funext t
    exact (Complex.ofRealCLM_apply t).symm
  have hrootC : HasDerivAt (fun t : ℝ => (Real.sqrt (1 - t ^ 2) : ℂ)) 0 0 := by
    simpa using hroot.ofReal_comp
  have hα : HasDerivAt
      (fun t : ℝ => (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I)
      (-Complex.I) 0 := by
    convert hrootC.sub (hcoe.mul_const Complex.I) using 1 <;> simp
  have hnum := ((hα.pow 2).mul_const ζ)
  have hden := ((hα.mul_const ζ).sub (hcoe.mul_const Complex.I))
  have hquot := hnum.div hden (by simpa using hζ)
  convert hquot using 1
  · funext t
    rfl
  · simp
    field_simp [hζ]
    ring

/-- Identifies the stable rational form with the displayed factor in
the manuscript wherever its denominator is nonzero. -/
theorem oddStarBoundaryFactor_eq_manuscript
    (ζ : ℂ) (t : ℝ) (hζ : ζ ≠ 0)
    (hα : (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I ≠ 0) :
    oddStarBoundaryFactor ζ t =
      ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) /
        (1 - (t : ℂ) * Complex.I /
          (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * ζ)) := by
  unfold oddStarBoundaryFactor
  have hp : (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * ζ) ≠ 0 :=
    mul_ne_zero hα hζ
  field_simp [hp]

/-- The principal logarithm has the same first variation at t=0. -/
theorem oddStarBoundaryFactor_log_hasDerivAt_zero
    (ζ : ℂ) (hζ : ζ ≠ 0) :
    HasDerivAt (fun t : ℝ => Complex.log (oddStarBoundaryFactor ζ t))
      (Complex.I * (ζ⁻¹ - 1)) 0 := by
  have hval : oddStarBoundaryFactor ζ 0 = 1 := by
    simp [oddStarBoundaryFactor, hζ]
  have hslit : oddStarBoundaryFactor ζ 0 ∈ Complex.slitPlane := by
    rw [hval, Complex.mem_slitPlane_iff]
    left
    norm_num
  convert (oddStarBoundaryFactor_hasDerivAt_zero ζ hζ).clog_real hslit using 1
  simp [hval]

/-- Trigonometric form of the logarithmic first variation. -/
theorem oddStarBoundaryFactor_log_derivative_angle (θ : ℝ) :
    Complex.I *
        ((Complex.exp ((θ : ℂ) * Complex.I))⁻¹ - 1) =
      (Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I := by
  rw [← Complex.exp_neg]
  have hneg : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hneg, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The exact angular first variation used in the paper's odd-order
integral comparison. -/
theorem oddStarBoundaryFactor_log_hasDerivAt_angle (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => Complex.log
        (oddStarBoundaryFactor (Complex.exp ((θ : ℂ) * Complex.I)) t))
      ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I) 0 := by
  have hζ : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  convert oddStarBoundaryFactor_log_hasDerivAt_zero _ hζ using 1
  exact (oddStarBoundaryFactor_log_derivative_angle θ).symm

end SpringerLean

#print axioms SpringerLean.oddStarBoundaryFactor_log_hasDerivAt_angle
