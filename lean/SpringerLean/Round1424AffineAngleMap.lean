import SpringerLean.Round1423AffineAmplification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace SpringerLean
set_option maxHeartbeats 200000

/-- The inverse angular map from the pure cosine model angle to the
original affine test angle. -/
noncomputable def refinedAffineAngle (γ φ : ℝ) : ℝ :=
  2*Real.arcsin (Real.sin (φ/2)/Real.sqrt γ)

/-- The argument of the arcsine has exactly the desired squared
projection deficit. -/
theorem refinedAffine_angle_argument_sq
    {γ φ : ℝ} (hγ : 0 < γ) :
    (Real.sin (φ/2)/Real.sqrt γ)^2 =
      (2-2*Real.cos φ)/(4*γ) := by
  have hsin : Real.sin (φ/2)^2 = (1-Real.cos φ)/2 := by
    convert Real.sin_sq_eq_half_sub (φ/2) using 1 <;> ring
  rw [div_pow, Real.sq_sqrt hγ.le, hsin]
  ring

/-- The inverse angular map is regular throughout the short active
arc; the arcsine argument remains well inside its domain. -/
theorem refinedAffine_angle_argument_range
    {γ φ : ℝ} (hγ : 0 < γ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Real.pi/2)
    (hshort : 2-2*Real.cos φ ≤ γ*(51/500:ℝ)) :
    0 ≤ Real.sin (φ/2)/Real.sqrt γ ∧
      Real.sin (φ/2)/Real.sqrt γ ≤ 1/4 := by
  have hφpi : φ/2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hsin : 0 ≤ Real.sin (φ/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hφpi
  have harg0 : 0 ≤ Real.sin (φ/2)/Real.sqrt γ :=
    div_nonneg hsin (Real.sqrt_nonneg _)
  have hsq := refinedAffine_angle_argument_sq (φ := φ) hγ
  have hsqLe : (Real.sin (φ/2)/Real.sqrt γ)^2 ≤ (51/2000:ℝ) := by
    rw [hsq]
    apply (div_le_iff₀ (by positivity : 0 < 4*γ)).2
    nlinarith
  constructor
  · exact harg0
  · nlinarith

/-- The short-arc angular map removes the affine projection dilation
exactly. Here `sφ` is the *model* projection deficit. -/
theorem refinedAffine_angle_deficit
    {γ φ : ℝ} (hγ : 0 < γ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Real.pi/2)
    (hshort : 2-2*Real.cos φ ≤ γ*(51/500:ℝ)) :
    γ*(2-2*Real.cos (refinedAffineAngle γ φ)) =
      2-2*Real.cos φ := by
  let q : ℝ := Real.sin (φ/2)/Real.sqrt γ
  obtain ⟨hq0,hq1⟩ := refinedAffine_angle_argument_range hγ hφ0 hφ hshort
  have hsin : Real.sin (Real.arcsin q) = q :=
    Real.sin_arcsin (by dsimp [q] at *; linarith)
      (by dsimp [q] at *; linarith)
  have hcos : Real.cos (2*Real.arcsin q) = 1-2*q^2 := by
    rw [Real.cos_two_mul]
    have htrig := Real.sin_sq_add_cos_sq (Real.arcsin q)
    rw [hsin] at htrig
    nlinarith
  have hsq := refinedAffine_angle_argument_sq (φ := φ) hγ
  change q^2 = _ at hsq
  have hqprod : 4*γ*q^2 = 2-2*Real.cos φ := by
    rw [hsq]
    field_simp [ne_of_gt hγ]
  unfold refinedAffineAngle
  change γ*(2-2*Real.cos (2*Real.arcsin q)) = _
  rw [hcos]
  nlinarith

theorem refinedAffine_angle_range
    {γ φ : ℝ} (hγ : 0 < γ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Real.pi/2)
    (hshort : 2-2*Real.cos φ ≤ γ*(51/500:ℝ)) :
    0 ≤ refinedAffineAngle γ φ ∧
      refinedAffineAngle γ φ ≤ Real.pi := by
  obtain ⟨hq0,_⟩ := refinedAffine_angle_argument_range hγ hφ0 hφ hshort
  unfold refinedAffineAngle
  constructor
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.2 hq0)
  · linarith [Real.arcsin_le_pi_div_two
      (Real.sin (φ/2)/Real.sqrt γ)]

end SpringerLean

#print axioms SpringerLean.refinedAffine_angle_argument_range
#print axioms SpringerLean.refinedAffine_angle_deficit
