import SpringerLean.Round1846ActualRadialTrace
import SpringerLean.Round39RotateExterior

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace SpringerLean

theorem polar_radius_eq_mul_unit (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) =
      (r : ℂ) * Complex.polarCoord.symm (1, θ) := by
  simp [Complex.polarCoord_symm_apply]

theorem polar_inv_radius_inverse (r θ : ℝ) :
    (Complex.polarCoord.symm (r⁻¹, θ))⁻¹ =
      conj (Complex.polarCoord.symm (r, θ)) := by
  have hunit : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by
    simp [Complex.norm_polarCoord_symm]
  rw [polar_radius_eq_mul_unit r⁻¹ θ, polar_radius_eq_mul_unit r θ]
  simp only [mul_inv_rev, Complex.inv_eq_conj hunit,
    ← Complex.ofReal_inv, inv_inv, map_mul, Complex.conj_ofReal]
  ring

theorem exterior_polar_forward_germ (F : ℂ → ℂ) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) :
    F (Complex.polarCoord.symm (r⁻¹, θ)) =
      Complex.polarCoord.symm (r⁻¹, θ) +
        exteriorForwardGerm F (conj (Complex.polarCoord.symm (r, θ))) := by
  have hu : conj (Complex.polarCoord.symm (r, θ)) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa only [← Complex.star_def, norm_star, Complex.norm_polarCoord_symm,
      abs_of_pos hr] using hr.ne'
  have h := exteriorForwardGerm_punctured F hu
  have hinv : (conj (Complex.polarCoord.symm (r, θ)))⁻¹ =
      Complex.polarCoord.symm (r⁻¹, θ) := by
    rw [← polar_inv_radius_inverse, inv_inv]
  rw [hinv] at h
  rw [h]
  abel

/-- The original exterior map's radial trace, at the original angle.
Its value on the exceptional null set is fixed by the primitive formula. -/
noncomputable def actualExteriorRadialTrace (F : ℂ → ℂ) (θ : ℝ) : ℂ :=
  Complex.polarCoord.symm (1, θ) + exteriorForwardConjugateRadialTrace F θ

/-- The trace is the limit along all reciprocal radii approaching one,
so it reads the actual exterior map and the correct conjugate angle. -/
theorem actualExteriorRadialTrace_ae_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      Tendsto (fun r : ℝ => F (Complex.polarCoord.symm (r⁻¹, θ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (actualExteriorRadialTrace F θ)) := by
  filter_upwards [exteriorForwardGerm_ae_conjugate_radial_limit F hc] with θ hθ
  have hp : Continuous (fun r : ℝ => Complex.polarCoord.symm (r, θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hi : ContinuousAt (fun r : ℝ => r⁻¹) 1 :=
    continuousAt_id.inv₀ (by norm_num)
  have hl : Tendsto (fun r : ℝ => Complex.polarCoord.symm (r⁻¹, θ))
      (𝓝[<] (1 : ℝ)) (𝓝 (Complex.polarCoord.symm (1, θ))) := by
    simpa only [Function.comp_def, inv_one] using
      (hp.continuousAt.comp hi).tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply (hl.add hθ).congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact (exterior_polar_forward_germ F hr.1 θ).symm

/-- Uniform domination near the boundary, without a bound on g'. -/
theorem exterior_polar_norm_le_radius_add_inv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    ‖F (Complex.polarCoord.symm (r⁻¹, θ))‖ ≤ r + r⁻¹ := by
  have heq : F (Complex.polarCoord.symm (r⁻¹, θ)) =
      actualHarmonic F (Complex.polarCoord.symm (r, θ)) +
        ((r⁻¹ - r : ℝ) : ℂ) * Complex.polarCoord.symm (1, θ) := by
    rw [exterior_polar_forward_germ F hr0 θ, actualHarmonic]
    rw [polar_radius_eq_mul_unit r⁻¹ θ, polar_radius_eq_mul_unit r θ]
    push_cast
    ring
  have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]
  have hnonneg : 0 ≤ r⁻¹ - r := by
    have hinv : 1 < r⁻¹ := (one_lt_inv₀ hr0).2 hr1
    linarith
  have hH := actualHarmonic_norm_le_two_norm F hc (z := Complex.polarCoord.symm (r, θ))
    (by simpa only [hnorm] using hr1)
  rw [hnorm] at hH
  rw [heq]
  calc
    _ ≤ ‖actualHarmonic F (Complex.polarCoord.symm (r, θ))‖ +
        ‖((r⁻¹ - r : ℝ) : ℂ) * Complex.polarCoord.symm (1, θ)‖ := norm_add_le _ _
    _ ≤ 2 * r + (r⁻¹ - r) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg,
        Complex.norm_polarCoord_symm]
      simpa using hH
    _ = r + r⁻¹ := by ring

end SpringerLean

#print axioms SpringerLean.actualExteriorRadialTrace_ae_tendsto
#print axioms SpringerLean.exterior_polar_norm_le_radius_add_inv
