import SpringerLean.Round1538PoissonTailKernel

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The cap and its complementary positive half arc partition the
Poisson kernel's unit mass. -/
theorem flattenedCapPoissonMass_complement
    {h r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hr0 : 0 < r) (hr1 : r < 1) :
    1-flattenedCapPoissonMass h r =
      Real.pi⁻¹ *
        (∫ θ in h..Real.pi,
          poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)) := by
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hInt1 : IntervalIntegrable P volume 0 h := hPc.intervalIntegrable _ _
  have hInt2 : IntervalIntegrable P volume h Real.pi := hPc.intervalIntegrable _ _
  have hsum : (∫ θ in (0:ℝ)..h,P θ)+
      (∫ θ in h..Real.pi,P θ)=Real.pi := by
    rw [intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
    exact centeredPoisson_half_interval_mass hr0 hr1
  dsimp [flattenedCapPoissonMass]
  rw [←intervalIntegral.integral_of_le hh0.le]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hunit : Real.pi⁻¹*Real.pi=1 := inv_mul_cancel₀ hpi
  nlinarith [mul_self_nonneg Real.pi]

/-- The Poisson mass outside the clipped arc is at most the simple
endpoint expression needed for the quantitative peak deficit. -/
theorem flattenedCapPoissonMass_tail_le
    {h r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hr0 : 0 < r) (hr1 : r < 1) :
    1-flattenedCapPoissonMass h r ≤
      (1-r^2)/(Real.pi*r*h) := by
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  let Q : ℝ → ℝ := fun θ =>
    ((1-r^2)/(4*r))*(1/Real.sin (θ/2)^2)
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hPInt : IntervalIntegrable P volume h Real.pi :=
    hPc.intervalIntegrable _ _
  have hsin : ∀ θ ∈ Icc h Real.pi, Real.sin (θ/2) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2,Real.pi_pos]))
  have hQcont : ContinuousOn Q (Icc h Real.pi) := by
    dsimp [Q]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro θ hθ
      exact pow_ne_zero _ (hsin θ hθ)
  have hQInt : IntervalIntegrable Q volume h Real.pi :=
    hQcont.intervalIntegrable_of_Icc hhpi.le
  have hraw : (∫ θ in h..Real.pi,P θ) ≤
      (1-r^2)/(4*r)*(2*Real.cos (h/2)/Real.sin (h/2)) := by
    have hcmp : (∫ θ in h..Real.pi,P θ) ≤
        ∫ θ in h..Real.pi,Q θ := by
      apply intervalIntegral.integral_mono_on hhpi.le hPInt hQInt
      intro θ hθ
      have hp := centeredPoisson_tail_pointwise hr0 hr1
        (by linarith [hθ.1]) hθ.2
      simpa [P,Q,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hp
    have hq : (∫ θ in h..Real.pi,Q θ) =
        (1-r^2)/(4*r)*(2*Real.cos (h/2)/Real.sin (h/2)) := by
      dsimp [Q]
      rw [intervalIntegral.integral_const_mul,
        reciprocalSineSquare_halfAngle_integral hh0 hhpi]
    exact hcmp.trans_eq hq
  have hcot := halfAngle_cotangent_le_two_div hh0 hhpi
  have hnum : 0 ≤ 1-r^2 := by nlinarith
  have hcoef : 0 ≤ (1-r^2)/(2*r) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcot hcoef
  have htail : (∫ θ in h..Real.pi,P θ) ≤ (1-r^2)/(r*h) := by
    calc
      _ ≤ (1-r^2)/(4*r)*(2*Real.cos (h/2)/Real.sin (h/2)) := hraw
      _ ≤ (1-r^2)/(r*h) := by
        convert hmul using 1 <;> ring
  rw [flattenedCapPoissonMass_complement hh0 hhpi hr0 hr1]
  have hπinv : 0 ≤ Real.pi⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htail hπinv
  have hπne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  convert hscaled using 1 <;> field_simp

end SpringerLean

#print axioms SpringerLean.flattenedCapPoissonMass_complement
#print axioms SpringerLean.flattenedCapPoissonMass_tail_le
