import SpringerLean.Round38CenteredWeighted

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Rotation of a centered exterior map by a unit complex number. -/
noncomputable def rotateExterior (ω : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  ω⁻¹ * F (ω * z)

/-- The rotated forward correction is the original analytic germ in
rotated local coordinates. -/
theorem rotateExterior_forwardGerm
    (F : ℂ → ℂ) (ω : ℂ) (hω : ‖ω‖ = 1) :
    exteriorForwardGerm (rotateExterior ω F) =
      fun t : ℂ => ω⁻¹ * exteriorForwardGerm F (ω⁻¹ * t) := by
  funext t
  have hω0 : ω ≠ 0 := by
    intro h
    simp [h] at hω
  by_cases ht : t = 0
  · simp [exteriorForwardGerm, ht]
  · have hlt : ω⁻¹ * t ≠ 0 := mul_ne_zero (inv_ne_zero hω0) ht
    simp only [exteriorForwardGerm_punctured _ ht,
      exteriorForwardGerm_punctured _ hlt, rotateExterior]
    field_simp


/-- Rotation preserves exactly the paper's original exterior function class. -/
theorem rotateExterior_centeredExteriorUnivalent
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ω : ℂ) (hω : ‖ω‖ = 1) :
    CenteredExteriorUnivalent (rotateExterior ω F) := by
  have hω0 : ω ≠ 0 := by
    intro hh
    simp [hh] at hω
  have hmap (z : ℂ) (hz : z ∈ exteriorDisk) : ω*z ∈ exteriorDisk := by
    change 1 < ‖ω*z‖
    rw [norm_mul, hω, one_mul]
    exact hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hF : DifferentiableAt ℂ F (ω*z) :=
      hc.1.differentiableAt (exteriorDisk_isOpen.mem_nhds (hmap z hz))
    have hlin : DifferentiableAt ℂ (fun u : ℂ => ω*u) z := by fun_prop
    have hcomp : DifferentiableAt ℂ (fun u : ℂ => F (ω*u)) z := by
      simpa [Function.comp_def] using hF.comp z hlin
    exact ((by fun_prop : DifferentiableAt ℂ (fun _ : ℂ => ω⁻¹) z).mul hcomp).differentiableWithinAt
  · intro z hz w hw heq
    have hF : F (ω*z) = F (ω*w) := by
      have hh := congrArg (fun u : ℂ => ω*u) heq
      simpa [rotateExterior, mul_assoc, hω0] using hh
    exact mul_left_cancel₀ hω0 (hc.2.1 (hmap z hz) (hmap w hw) hF)
  · rw [rotateExterior_forwardGerm F ω hω]
    have hlin : AnalyticAt ℂ (fun t : ℂ => ω⁻¹*t) 0 := by fun_prop
    have hcomp : AnalyticAt ℂ
        (fun t : ℂ => exteriorForwardGerm F (ω⁻¹*t)) 0 := by
      have hgf : AnalyticAt ℂ (exteriorForwardGerm F) ((fun t : ℂ => ω⁻¹*t) 0) := by
        simpa using hc.2.2
      simpa [Function.comp_def] using hgf.comp hlin
    exact analyticAt_const.mul hcomp

/-- Harmonic filling commutes with rotating the actual exterior map. -/
theorem rotateExterior_regularHarmonic
    (F : ℂ → ℂ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (s : ℝ) (z : ℂ) :
    regularHarmonic s (rotateExterior ω F) z =
      ω⁻¹ * regularHarmonic s F (ω*z) := by
  have hconj : conj (ω*z) = ω⁻¹ * conj z := by
    rw [map_mul, Complex.inv_eq_conj hω]
  simp only [regularHarmonic, regularForwardGerm,
    rotateExterior_forwardGerm F ω hω, hconj]
  have hω0 : ω ≠ 0 := by
    intro hh
    simp [hh] at hω
  field_simp [hω0] <;> ring

/-- The same rotation identity holds for the original filling. -/
theorem rotateExterior_actualHarmonic
    (F : ℂ → ℂ) (ω : ℂ) (hω : ‖ω‖ = 1) (z : ℂ) :
    actualHarmonic (rotateExterior ω F) z =
      ω⁻¹ * actualHarmonic F (ω*z) := by
  have hconj : conj (ω*z) = ω⁻¹ * conj z := by
    rw [map_mul, Complex.inv_eq_conj hω]
  simp only [actualHarmonic, rotateExterior_forwardGerm F ω hω, hconj]
  have hω0 : ω ≠ 0 := by
    intro hh
    simp [hh] at hω
  field_simp [hω0] <;> ring

/-- The sharp pointwise estimate for the actual harmonic filling of every
map in the paper's original centered exterior class. -/
theorem actualHarmonic_norm_le_two_norm
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖actualHarmonic F z‖ ≤ 2 * ‖z‖ := by
  by_cases hz0 : z = 0
  · subst z
    simp [actualHarmonic, exteriorForwardGerm_zero]
  let r : ℝ := ‖z‖
  let ω : ℂ := z / (r : ℂ)
  have hr0 : 0 < r := norm_pos_iff.mpr hz0
  have hr1 : r < 1 := hz
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hω : ‖ω‖ = 1 := by
    simp [ω, r, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hrne]
  have hωz : ω * (r : ℂ) = z := by
    dsimp [ω]
    field_simp [hrne]
  have hrot : CenteredExteriorUnivalent (rotateExterior ω F) :=
    rotateExterior_centeredExteriorUnivalent F hc ω hω
  have hbound := actualHarmonic_centered_norm_le_two_radius
    (rotateExterior ω F) hrot hr0 hr1
  rw [rotateExterior_actualHarmonic F ω hω, hωz,
    norm_mul, norm_inv, hω, inv_one, one_mul] at hbound
  exact hbound
end SpringerLean