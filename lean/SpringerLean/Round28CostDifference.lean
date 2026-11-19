import SpringerLean.Round28PotentialUniformStrip

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- An exact finite-mass estimate for changing the integrand of a
measurable cost set. -/
theorem abs_setIntegral_sub_le_of_uniform_bound
    (E : Set ℝ) (hE : MeasurableSet E) (hEfin : volume E ≠ ∞)
    (f g : ℝ → ℝ) (hf : IntegrableOn f E) (hg : IntegrableOn g E)
    (η : ℝ) (hη : 0 ≤ η)
    (hbound : ∀ t ∈ E, |f t - g t| ≤ η) :
    |(∫ t in E, f t) - (∫ t in E, g t)| ≤ η * volume.real E := by
  have hdiff := hf.sub hg
  have hle : (∫ t in E, |f t - g t|) ≤ ∫ _t in E, η := by
    apply integral_mono_ae hdiff.abs (integrableOn_const hEfin)
    exact (ae_restrict_iff' hE).2 (Filter.Eventually.of_forall hbound)
  calc
    |(∫ t in E, f t) - (∫ t in E, g t)| =
      |∫ t in E, f t - g t| := by rw [integral_sub hf hg]
    _ ≤ ∫ t in E, |f t - g t| := abs_integral_le_integral_abs
    _ ≤ ∫ _t in E, η := hle
    _ = η * volume.real E := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]

end SpringerLean