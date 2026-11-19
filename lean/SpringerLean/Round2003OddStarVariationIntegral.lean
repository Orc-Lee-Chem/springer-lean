import SpringerLean.Round2002OddStarOppositeTipFormula
import SpringerLean.Round30AnglePair
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory

namespace SpringerLean

/-- Cancellation of an odd periodic angular integral. -/
theorem periodic_odd_angle_integral_zero
    (f : ℝ → ℝ) (hper : Function.Periodic f (2 * Real.pi))
    (hodd : ∀ θ, f (-θ) = -f θ)
    (hint : IntervalIntegrable f volume (-Real.pi) Real.pi) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) = 0 := by
  rw [periodic_angle_integral_pair f hper hint]
  simp [hodd]

/-- The radial term in the pointwise opposite-tip variation. -/
noncomputable def oddStarRadialDerivativeTerm (m : ℕ) (θ : ℝ) : ℝ :=
  let r := oddStarBoundaryRadius m θ
  let R := oddStarTipRadius m 0
  let δ := Real.pi - Real.pi / (m : ℝ)
  (r / (m : ℝ)) * (r - R * Real.cos δ) * Real.sin θ /
    (r ^ 2 + R ^ 2 - 2 * r * R * Real.cos δ)

theorem oddStarBoundaryRadius_continuous (m : ℕ) (hm : 3 ≤ m) :
    Continuous (oddStarBoundaryRadius m) := by
  unfold oddStarBoundaryRadius
  apply (Real.continuous_rpow_const (by positivity : 0 ≤ ((m : ℝ)⁻¹))).comp
  fun_prop

theorem oddStarRadialDerivativeTerm_continuous (m : ℕ) (hm : 3 ≤ m) :
    Continuous (oddStarRadialDerivativeTerm m) := by
  have hr := oddStarBoundaryRadius_continuous m hm
  have hnum : Continuous (fun θ : ℝ =>
      (oddStarBoundaryRadius m θ / (m : ℝ)) *
        (oddStarBoundaryRadius m θ - oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ))) * Real.sin θ) := by
    fun_prop
  have hden : Continuous (fun θ : ℝ =>
      (oddStarBoundaryRadius m θ) ^ 2 + (oddStarTipRadius m 0) ^ 2 -
        2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ))) := by
    fun_prop
  change Continuous (fun θ : ℝ =>
    ((oddStarBoundaryRadius m θ / (m : ℝ)) *
      (oddStarBoundaryRadius m θ - oddStarTipRadius m 0 *
        Real.cos (Real.pi - Real.pi / (m : ℝ))) * Real.sin θ) /
      ((oddStarBoundaryRadius m θ) ^ 2 + (oddStarTipRadius m 0) ^ 2 -
        2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ))))
  exact hnum.div hden (fun θ => (oddStarOppositeTip_denominator_pos m hm θ).ne')

theorem oddStarRadialDerivativeTerm_odd (m : ℕ) (θ : ℝ) :
    oddStarRadialDerivativeTerm m (-θ) =
      -oddStarRadialDerivativeTerm m θ := by
  simp [oddStarRadialDerivativeTerm, oddStarBoundaryRadius,
    Real.cos_neg, Real.sin_neg]
  ring

theorem oddStarRadialDerivativeTerm_periodic (m : ℕ) :
    Function.Periodic (oddStarRadialDerivativeTerm m) (2 * Real.pi) := by
  intro θ
  simp [oddStarRadialDerivativeTerm, oddStarBoundaryRadius,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem oddStarRadialDerivativeTerm_integral_zero
    (m : ℕ) (hm : 3 ≤ m) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarRadialDerivativeTerm m θ) = 0 := by
  have hc := oddStarRadialDerivativeTerm_continuous m hm
  exact periodic_odd_angle_integral_zero _
    (oddStarRadialDerivativeTerm_periodic m)
    (oddStarRadialDerivativeTerm_odd m)
    (hc.intervalIntegrable _ _)

/-- The nonnegative angular term in the pointwise variation. -/
noncomputable def oddStarAngularDerivativeTerm (m : ℕ) (θ : ℝ) : ℝ :=
  let r := oddStarBoundaryRadius m θ
  let R := oddStarTipRadius m 0
  let δ := Real.pi - Real.pi / (m : ℝ)
  (r / (m : ℝ)) * R * Real.sin δ * (1 - Real.cos θ) /
    (r ^ 2 + R ^ 2 - 2 * r * R * Real.cos δ)

theorem oddStarAngularDerivativeTerm_continuous (m : ℕ) (hm : 3 ≤ m) :
    Continuous (oddStarAngularDerivativeTerm m) := by
  have hr := oddStarBoundaryRadius_continuous m hm
  have hnum : Continuous (fun θ : ℝ =>
      (oddStarBoundaryRadius m θ / (m : ℝ)) *
        oddStarTipRadius m 0 *
          Real.sin (Real.pi - Real.pi / (m : ℝ)) *
          (1 - Real.cos θ)) := by
    fun_prop
  have hden : Continuous (fun θ : ℝ =>
      (oddStarBoundaryRadius m θ) ^ 2 + (oddStarTipRadius m 0) ^ 2 -
        2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ))) := by
    fun_prop
  change Continuous (fun θ : ℝ =>
    ((oddStarBoundaryRadius m θ / (m : ℝ)) *
      oddStarTipRadius m 0 * Real.sin (Real.pi - Real.pi / (m : ℝ)) *
      (1 - Real.cos θ)) /
      ((oddStarBoundaryRadius m θ) ^ 2 + (oddStarTipRadius m 0) ^ 2 -
        2 * oddStarBoundaryRadius m θ * oddStarTipRadius m 0 *
          Real.cos (Real.pi - Real.pi / (m : ℝ))))
  exact hnum.div hden (fun θ => (oddStarOppositeTip_denominator_pos m hm θ).ne')

theorem oddStarAngularDerivativeTerm_nonneg
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    0 ≤ oddStarAngularDerivativeTerm m θ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrbase : 0 ≤ 2 + 2 * Real.cos θ := by
    nlinarith [Real.neg_one_le_cos θ]
  have hr : 0 ≤ oddStarBoundaryRadius m θ := by
    unfold oddStarBoundaryRadius
    exact Real.rpow_nonneg hrbase _
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hsin : 0 < Real.sin (Real.pi - Real.pi / (m : ℝ)) :=
    (oddStar_opposite_tip_angle_geometry m hm 0 0 (le_refl _) (le_refl _)).1
  have hcos : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
  have hD := oddStarOppositeTip_denominator_pos m hm θ
  unfold oddStarAngularDerivativeTerm
  positivity

theorem oddStarAngularDerivativeTerm_pos_at_halfpi
    (m : ℕ) (hm : 3 ≤ m) :
    0 < oddStarAngularDerivativeTerm m (Real.pi / 2) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr : 0 < oddStarBoundaryRadius m (Real.pi / 2) := by
    simp [oddStarBoundaryRadius, Real.cos_pi_div_two]
    positivity
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hsin : 0 < Real.sin (Real.pi - Real.pi / (m : ℝ)) :=
    (oddStar_opposite_tip_angle_geometry m hm 0 0 (le_refl _) (le_refl _)).1
  have hD := oddStarOppositeTip_denominator_pos m hm (Real.pi / 2)
  unfold oddStarAngularDerivativeTerm
  simp only [Real.cos_pi_div_two, sub_zero]
  positivity

theorem oddStarAngularDerivativeTerm_integral_pos
    (m : ℕ) (hm : 3 ≤ m) :
    0 < (∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarAngularDerivativeTerm m θ) := by
  have hc := oddStarAngularDerivativeTerm_continuous m hm
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos]) hc.continuousOn
  · intro θ hθ
    exact oddStarAngularDerivativeTerm_nonneg m hm θ
  · refine ⟨Real.pi / 2, ?_, oddStarAngularDerivativeTerm_pos_at_halfpi m hm⟩
    constructor <;> linarith [Real.pi_pos]

/-- The exact scalar derivative of the opposite-tip logarithmic
distance at parameter t=0. -/
noncomputable def oddStarPointwiseVariation (m : ℕ) (θ : ℝ) : ℝ :=
  let r := oddStarBoundaryRadius m θ
  let R := oddStarTipRadius m 0
  let δ := Real.pi - Real.pi / (m : ℝ)
  (r / (m : ℝ)) *
    ((r - R * Real.cos δ) * Real.sin θ +
      R * Real.sin δ * (1 - Real.cos θ)) /
    (r ^ 2 + R ^ 2 - 2 * r * R * Real.cos δ)

theorem oddStarPointwiseVariation_split (m : ℕ) (θ : ℝ) :
    oddStarPointwiseVariation m θ =
      oddStarRadialDerivativeTerm m θ +
        oddStarAngularDerivativeTerm m θ := by
  unfold oddStarPointwiseVariation oddStarRadialDerivativeTerm
    oddStarAngularDerivativeTerm
  ring

theorem oddStarPointwiseVariation_integral_pos
    (m : ℕ) (hm : 3 ≤ m) :
    0 < (∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarPointwiseVariation m θ) := by
  simp_rw [oddStarPointwiseVariation_split]
  have hr : IntervalIntegrable (oddStarRadialDerivativeTerm m) volume
      (0 : ℝ) (2 * Real.pi) :=
    (oddStarRadialDerivativeTerm_continuous m hm).intervalIntegrable _ _
  have ha : IntervalIntegrable (oddStarAngularDerivativeTerm m) volume
      (0 : ℝ) (2 * Real.pi) :=
    (oddStarAngularDerivativeTerm_continuous m hm).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hr ha,
    oddStarRadialDerivativeTerm_integral_zero m hm, zero_add]
  exact oddStarAngularDerivativeTerm_integral_pos m hm

end SpringerLean

#print axioms SpringerLean.oddStarRadialDerivativeTerm_integral_zero
#print axioms SpringerLean.oddStarAngularDerivativeTerm_integral_pos
#print axioms SpringerLean.oddStarPointwiseVariation_integral_pos
