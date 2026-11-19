import SpringerLean.Round83ComplexBoundary
import SpringerLean.Round14QuadraticPrelude
import SpringerLean.UniformDerivative

namespace SpringerLean

open scoped ComplexConjugate Topology

/-- The actual regularized exterior map has its genuine convergent
Laurent expansion at each point of the unit circle. The coefficients
belong to the same original `F` used by the inverse coefficient interface.
Uniform convergence of the angular derivative is a separate obligation. -/
theorem rescaleExterior_boundary_laurent_hasSum
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    HasSum (fun j : ℕ =>
      (s : ℂ) ^ (j + 1) * exteriorForwardCoeff F j * (z⁻¹) ^ j)
      (rescaleExterior s F z - z) := by
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hz
  have hsu : ‖(s : ℂ) * z⁻¹‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, norm_inv, hz]
    norm_num
    exact hs1
  have h := (exteriorForwardGerm_hasSum_coeff_unitBall F hc hsu).mul_left (s : ℂ)
  have hident : (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * z⁻¹) =
      rescaleExterior s F z - z := by
    rw [← rescaleExterior_forwardGerm s hs0 F z⁻¹]
    rw [exteriorForwardGerm_punctured _ (inv_ne_zero hz0), inv_inv]
  convert h using 1
  · funext j
    rw [mul_pow]
    ring
  · exact hident.symm


/-- The actual forward correction of `F_s` is the uniform limit of its
coefficient partial sums on the entire unit circle. The radius `s<1`
allows the existing unit-disk analytic Taylor theorem to apply. -/
theorem rescaleExterior_boundary_germ_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        ∑ j ∈ Finset.range M,
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1) θ) ^ j)
      (fun θ : AddCircle (2 * Real.pi) =>
        exteriorForwardGerm F ((s : ℂ) * fourier (-1) θ))
      Filter.atTop Set.univ := by
  obtain ⟨r, hsr, hr1⟩ := exists_between hs1
  have hrnonneg : 0 ≤ r := by linarith
  let rnn : NNReal := ⟨r, hrnonneg⟩
  have hbase := exteriorForwardGerm_uniform_on_subdisk F hc
    (r := rnn) (by change r < 1; exact hr1)
  let point : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => (s : ℂ) * fourier (-1) θ
  have hsubset : Set.univ ⊆ point ⁻¹' Metric.ball (0 : ℂ) rnn := by
    intro θ hθ
    change dist (point θ) 0 < r
    rw [dist_zero_right]
    change ‖(s : ℂ) * fourier (-1) θ‖ < r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      fourier_apply, Circle.norm_coe, mul_one]
    exact hsr
  exact (hbase.comp point).mono hsubset

/-- The derivative of the same actual forward germ also has uniformly
convergent coefficient partial sums at every regularized unit-circle
argument. This is the analytic tail control needed for angular derivatives. -/
theorem rescaleExterior_boundary_germ_deriv_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        ∑ j ∈ Finset.range M,
          (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) *
            ((s : ℂ) * fourier (-1) θ) ^ j)
      (fun θ : AddCircle (2 * Real.pi) =>
        deriv (exteriorForwardGerm F) ((s : ℂ) * fourier (-1) θ))
      Filter.atTop Set.univ := by
  obtain ⟨r, hsr, hr1⟩ := exists_between hs1
  have hrnonneg : 0 ≤ r := by linarith
  let rnn : NNReal := ⟨r, hrnonneg⟩
  have hbase := exteriorForwardGerm_deriv_uniform_on_subdisk F hc
    (r := rnn) (by change r < 1; exact hr1)
  let point : AddCircle (2 * Real.pi) → ℂ :=
    fun θ => (s : ℂ) * fourier (-1) θ
  have hsubset : Set.univ ⊆ point ⁻¹' Metric.ball (0 : ℂ) rnn := by
    intro θ hθ
    change dist (point θ) 0 < r
    rw [dist_zero_right]
    change ‖(s : ℂ) * fourier (-1) θ‖ < r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0,
      fourier_apply, Circle.norm_coe, mul_one]
    exact hsr
  exact (hbase.comp point).mono hsubset

/-- Uniform convergence after the regularization scalar factor. This is
the actual forward correction of the map `F_s` along the unit circle. -/
theorem rescaleExterior_boundary_scaled_germ_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        (s : ℂ) * (∑ j ∈ Finset.range M,
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1) θ) ^ j))
      (fun θ : AddCircle (2 * Real.pi) =>
        (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * fourier (-1) θ))
      Filter.atTop Set.univ := by
  simpa only [Function.comp_def, smul_eq_mul] using
    (uniformContinuous_const_smul (s : ℂ)).comp_tendstoUniformlyOn
      (rescaleExterior_boundary_germ_uniform F hc hs0 hs1)

/-- The Fourier circle value is the genuine boundary value of the
regularized map, not merely a formal germ evaluation. -/
theorem rescaleExterior_boundary_value_fourier
    (F : ℂ → ℂ) {s : ℝ} (hs0 : 0 < s)
    (θ : AddCircle (2 * Real.pi)) :
    rescaleExterior s F (fourier 1 θ) =
      fourier 1 θ + (s : ℂ) *
        exteriorForwardGerm F ((s : ℂ) * fourier (-1) θ) := by
  have hnorm : ‖fourier (T := 2 * Real.pi) 1 θ‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  rw [rescaleExterior_unitCircle_eq_harmonic F hs0 hnorm]
  rw [fourier_neg]

/-- Uniform convergence on the true boundary curve of the actual regularized
exterior map, with no extra boundary regularity assumption. -/
theorem rescaleExterior_boundary_actual_laurent_uniform
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : AddCircle (2 * Real.pi) =>
        (s : ℂ) * (∑ j ∈ Finset.range M,
          exteriorForwardCoeff F j *
            ((s : ℂ) * fourier (-1) θ) ^ j))
      (fun θ : AddCircle (2 * Real.pi) =>
        rescaleExterior s F (fourier 1 θ) - fourier 1 θ)
      Filter.atTop Set.univ := by
  apply (rescaleExterior_boundary_scaled_germ_uniform F hc hs0 hs1).congr_right
  intro θ hθ
  change (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * fourier (-1) θ) =
    rescaleExterior s F (fourier 1 θ) - fourier 1 θ
  rw [rescaleExterior_boundary_value_fourier F hs0 θ]
  ring
end SpringerLean