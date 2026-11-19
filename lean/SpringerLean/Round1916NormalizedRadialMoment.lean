import SpringerLean.Round1915ActualInterpolationTest

open MeasureTheory Set

namespace SpringerLean

noncomputable def normalizedActualRadialMoment
    (F : ℂ → ℂ) (p : ℝ) : ℝ :=
  actualBoundaryRadialMoment F p / (2 : ℝ) ^ p

noncomputable def normalizedCosineMoment (p : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ => |z.re| ^ p) 0 1

theorem normalizedActualRadialMoment_eq_integral
    (F : ℂ → ℂ) (p : ℝ) :
    normalizedActualRadialMoment F p =
      (2 * Real.pi)⁻¹ *
        ∫ θ in Ioo (-Real.pi) Real.pi,
          (‖actualExteriorRadialTrace F θ‖ / 2) ^ p := by
  have hpoint (θ : ℝ) :
      (‖actualExteriorRadialTrace F θ‖ / 2) ^ p =
        ‖actualExteriorRadialTrace F θ‖ ^ p / (2 : ℝ) ^ p := by
    rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [hpoint]
  rw [integral_div]
  unfold normalizedActualRadialMoment actualBoundaryRadialMoment
  ring

end SpringerLean

#print axioms SpringerLean.normalizedActualRadialMoment_eq_integral
