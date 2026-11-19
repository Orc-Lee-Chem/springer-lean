import SpringerLean.Round12CompareMoments
import SpringerLean.Round12HullParameter
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- Reflection of the angular parameter preserves circle average at the
origin, at every real radius. -/
theorem circleAverage_comp_conj_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (r : ℝ) :
    Real.circleAverage (fun z : ℂ => f (conj z)) 0 r =
      Real.circleAverage f 0 r := by
  unfold Real.circleAverage
  congr 1
  calc
    (∫ θ in 0..2 * Real.pi, f (conj (circleMap 0 r θ))) =
        ∫ θ in 0..2 * Real.pi, f (circleMap 0 r (-θ)) := by
          simp_rw [conj_circleMap_zero]
    _ = ∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ) := by
      rw [intervalIntegral.integral_comp_neg
        (fun w => f (circleMap 0 r w))]
      have hper : Function.Periodic
          (fun θ : ℝ => f (circleMap 0 r θ)) (2 * Real.pi) :=
        fun θ => by simp [periodic_circleMap 0 r θ]
      simpa using (hper.intervalIntegral_add_eq (-(2 * Real.pi)) 0)

/-- The actual forward correction has zero angular mean on every inner
circle. This uses its analyticity on the *whole* open unit disk. -/
theorem exteriorForwardGerm_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (exteriorForwardGerm F) 0 r = 0 := by
  have hAnal := exteriorForwardGerm_analyticOnNhd_unitBall F hc
  have hsub : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    intro z hz
    rw [abs_of_nonneg hr0] at hz
    exact lt_of_le_of_lt hz hr1
  have hcont : ContinuousOn (exteriorForwardGerm F)
      (Metric.closedBall (0 : ℂ) |r|) :=
    hAnal.continuousOn.mono hsub
  have hdiff : ∀ z ∈ Metric.ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (exteriorForwardGerm F) z := by
    intro z hz
    exact (hAnal z (hsub (Metric.ball_subset_closedBall hz.1))).differentiableAt
  simpa only [exteriorForwardGerm_zero] using
    (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff)

/-- The actual harmonic filling has zero complex mean on every inner circle. -/
theorem actualHarmonic_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (actualHarmonic F) 0 r = 0 := by
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 1 := by
    intro z hz
    exact lt_of_le_of_lt hz hr1
  have hG : ContinuousOn (exteriorForwardGerm F)
      (Metric.closedBall (0 : ℂ) r) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.mono hsub
  have hC : ContinuousOn (fun z : ℂ => exteriorForwardGerm F (conj z))
      (Metric.closedBall (0 : ℂ) r) := by
    apply hG.comp Complex.continuous_conj.continuousOn
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right,
      Complex.norm_conj] using hz
  have hI : CircleIntegrable (fun z : ℂ => z) 0 r :=
    continuousOn_id.circleIntegrable hr0
  have hC' : CircleIntegrable
      (fun z : ℂ => exteriorForwardGerm F (conj z)) 0 r :=
    (hC.mono Metric.sphere_subset_closedBall).circleIntegrable hr0
  have hIme : Real.circleAverage (fun z : ℂ => z) 0 r = 0 := by
    change Real.circleAverage id 0 r = 0
    exact (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty continuousOn_id
      (fun z _ => differentiableAt_id))
  have hGme := exteriorForwardGerm_circleAverage_zero F hc hr0 hr1
  calc
    Real.circleAverage (actualHarmonic F) 0 r =
        Real.circleAverage (fun z : ℂ => z) 0 r +
          Real.circleAverage (fun z : ℂ => exteriorForwardGerm F (conj z)) 0 r := by
            change Real.circleAverage
              (fun z : ℂ => z + exteriorForwardGerm F (conj z)) 0 r = _
            exact Real.circleAverage_fun_add hI hC'
    _ = 0 := by rw [hIme, circleAverage_comp_conj_zero,
      hGme, zero_add]

/-- The actual projected inner-circle variable has mean zero for every
direction. `Real.circleAverage` is the angle integral divided by `2π`. -/
theorem actualHarmonic_projection_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z : ℂ => ((conj ξ) * actualHarmonic F z).re) 0 r = 0 := by
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 1 := by
    intro z hz
    exact lt_of_le_of_lt hz hr1
  have hG : ContinuousOn (exteriorForwardGerm F)
      (Metric.closedBall (0 : ℂ) r) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.mono hsub
  have hC : ContinuousOn (fun z : ℂ => exteriorForwardGerm F (conj z))
      (Metric.closedBall (0 : ℂ) r) := by
    apply hG.comp Complex.continuous_conj.continuousOn
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right,
      Complex.norm_conj] using hz
  have hHcont : ContinuousOn (actualHarmonic F)
      (Metric.closedBall (0 : ℂ) r) := by
    change ContinuousOn (fun z : ℂ => z + exteriorForwardGerm F (conj z)) _
    exact continuousOn_id.add hC
  have hWcont : ContinuousOn
      (fun z : ℂ => (conj ξ) • actualHarmonic F z)
      (Metric.sphere (0 : ℂ) r) := by
    change ContinuousOn (fun z : ℂ => conj ξ * actualHarmonic F z) _
    exact continuousOn_const.mul
      (hHcont.mono Metric.sphere_subset_closedBall)
  have hWint : CircleIntegrable
      (fun z : ℂ => (conj ξ) • actualHarmonic F z) 0 r :=
    hWcont.circleIntegrable hr0
  have hmean := actualHarmonic_circleAverage_zero F hc hr0 hr1
  calc
    Real.circleAverage
        (fun z : ℂ => ((conj ξ) * actualHarmonic F z).re) 0 r =
      Complex.reCLM (Real.circleAverage
        (fun z : ℂ => (conj ξ) • actualHarmonic F z) 0 r) := by
          simpa only [smul_eq_mul, Function.comp_def, Complex.reCLM_apply] using
            (Complex.reCLM.circleAverage_comp_comm hWint)
    _ = 0 := by rw [Real.circleAverage_fun_smul, hmean]; simp

/-- The comparison circle variable `2 r cos θ`, expressed on the actual
circle of radius `r`, also has mean zero. -/
theorem comparisonCircle_projection_circleAverage_zero
    {r : ℝ} (hr0 : 0 ≤ r) :
    Real.circleAverage (fun z : ℂ => 2 * z.re) 0 r = 0 := by
  have hI : Real.circleAverage (fun z : ℂ => z) 0 r = 0 := by
    change Real.circleAverage id 0 r = 0
    exact circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty continuousOn_id
      (fun z _ => differentiableAt_id)
  have hInt : CircleIntegrable (fun z : ℂ => z) 0 r :=
    continuousOn_id.circleIntegrable hr0
  have hRe : Real.circleAverage (fun z : ℂ => z.re) 0 r = 0 := by
    have h := Complex.reCLM.circleAverage_comp_comm hInt
    simpa [Function.comp_def, Complex.reCLM_apply, hI] using h
  calc
    Real.circleAverage (fun z : ℂ => 2 * z.re) 0 r =
        (2 : ℝ) • Real.circleAverage (fun z : ℂ => z.re) 0 r := by
          simpa only [smul_eq_mul] using
            (Real.circleAverage_fun_smul (a := (2 : ℝ))
              (f := fun z : ℂ => z.re) (c := (0 : ℂ)) (R := r))
    _ = 0 := by rw [hRe]; simp

end SpringerLean
