import SpringerLean.Round14JensenSimple
import SpringerLean.Round14CircleParseval

open MeasureTheory Metric AddCircle
open scoped ComplexConjugate

namespace SpringerLean

/-- The regularized forward correction has zero complex mean on its actual
unit-circle boundary. -/
theorem regularForwardGerm_boundary_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (regularForwardGerm s F) 0 1 = 0 := by
  have hInv : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  have hAnal := regularForwardGerm_analyticOnNhd F hc hs0
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
    intro z hz
    exact lt_of_le_of_lt hz hInv
  have hcont : ContinuousOn (regularForwardGerm s F)
      (closedBall (0 : ℂ) 1) := hAnal.continuousOn.mono hsub
  have hdiff : ∀ z ∈ ball (0 : ℂ) 1 \ (∅ : Set ℂ),
      DifferentiableAt ℂ (regularForwardGerm s F) z := by
    intro z hz
    exact (hAnal z (hsub (ball_subset_closedBall hz.1))).differentiableAt
  have hcont' : ContinuousOn (regularForwardGerm s F)
      (closedBall (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hcont
  have hdiff' : ∀ z ∈ ball (0 : ℂ) |(1 : ℝ)| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (regularForwardGerm s F) z := by
    simpa only [abs_one] using hdiff
  simpa only [regularForwardGerm, exteriorForwardGerm_zero,
    mul_zero, zero_mul] using
    (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty hcont' hdiff')

/-- The actual smooth exterior boundary curve has zero complex angular mean. -/
theorem rescaleExterior_boundary_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (rescaleExterior s F) 0 1 = 0 := by
  have hInv : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  have hAnal := regularForwardGerm_analyticOnNhd F hc hs0
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
    intro z hz
    exact lt_of_le_of_lt hz hInv
  have hG : ContinuousOn (regularForwardGerm s F)
      (closedBall (0 : ℂ) 1) := hAnal.continuousOn.mono hsub
  have hC : ContinuousOn (fun z : ℂ => regularForwardGerm s F (conj z))
      (closedBall (0 : ℂ) 1) := by
    apply hG.comp Complex.continuous_conj.continuousOn
    intro z hz
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
  have hI : CircleIntegrable (fun z : ℂ => z) 0 1 :=
    continuousOn_id.circleIntegrable (by norm_num)
  have hC' : CircleIntegrable
      (fun z : ℂ => regularForwardGerm s F (conj z)) 0 1 :=
    (hC.mono sphere_subset_closedBall).circleIntegrable (by norm_num)
  have hId : Real.circleAverage (fun z : ℂ => z) 0 1 = 0 := by
    change Real.circleAverage id 0 1 = 0
    exact (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty continuousOn_id
      (fun z _ => differentiableAt_id))
  calc
    Real.circleAverage (rescaleExterior s F) 0 1 =
        Real.circleAverage (regularHarmonic s F) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          have hnorm : ‖z‖ = 1 := by
            simpa only [mem_sphere, dist_zero_right, abs_one] using hz
          exact (regularHarmonic_unitCircle_eq_actual F hs0 hnorm).symm
    _ = Real.circleAverage (fun z : ℂ => z) 0 1 +
          Real.circleAverage (fun z : ℂ => regularForwardGerm s F (conj z)) 0 1 := by
            change Real.circleAverage
              (fun z : ℂ => z + regularForwardGerm s F (conj z)) 0 1 = _
            exact Real.circleAverage_fun_add hI hC'
    _ = 0 := by
          rw [hId, circleAverage_comp_conj_zero,
            regularForwardGerm_boundary_circleAverage_zero F hc hs0 hs1]
          simp

/-- Every complex directional rotation of the actual regularized boundary
curve has complex mean zero; its real projection therefore has mean zero. -/
theorem rescaleExterior_projected_boundary_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    Real.circleAverage
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re) 0 1 = 0 := by
  have hComplex : Real.circleAverage
      (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ) 0 1 = 0 := by
    rw [circleAverage_eq_haar_circle_complex]
    rw [integral_const_mul]
    rw [← circleAverage_eq_haar_circle_complex]
    rw [rescaleExterior_boundary_circleAverage_zero F hc hs0 hs1]
    simp
  have hcont : ContinuousOn (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ)
      (sphere (0 : ℂ) 1) := by
    have hF : ∀ z ∈ sphere (0 : ℂ) 1,
        AnalyticAt ℂ (rescaleExterior s F) z := by
      intro z hz
      have hnorm : ‖z‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hz
      have hext : z ∈ exteriorAbove s := by
        change s < ‖z‖
        rw [hnorm]
        exact hs1
      have hFa : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
        fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
      exact (rescaleExterior_analyticAt hs0 hFa hext)
    exact (fun z hz => (analyticAt_const.mul (hF z hz)).continuousAt.continuousWithinAt)
  have hInt : CircleIntegrable
      (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  have hpcont : Continuous (exteriorCirclePoint (1 : ℝ)) := by
    unfold exteriorCirclePoint
    fun_prop
  have hpSphere : ∀ θ : AddCircle (2 * Real.pi),
      exteriorCirclePoint (1 : ℝ) θ ∈ sphere (0 : ℂ) 1 := by
    intro θ
    simpa [mem_sphere, dist_zero_right] using exteriorCirclePoint_norm (by norm_num) θ
  have hcomp : Continuous (fun θ : AddCircle (2 * Real.pi) =>
      conj ξ * rescaleExterior s F (exteriorCirclePoint 1 θ)) :=
    hcont.comp_continuous hpcont hpSphere
  have hHaar : Integrable (fun θ : AddCircle (2 * Real.pi) =>
      conj ξ * rescaleExterior s F (exteriorCirclePoint 1 θ)) haarAddCircle := by
    simpa [IntegrableOn] using hcomp.continuousOn.integrableOn_compact
      (μ := haarAddCircle) isCompact_univ
  have hRe :
      Real.circleAverage
        (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re) 0 1 =
      (Real.circleAverage (fun ζ : ℂ => conj ξ * rescaleExterior s F ζ) 0 1).re := by
    rw [circleAverage_eq_haar_circle, circleAverage_eq_haar_circle_complex]
    simpa only [RCLike.re_eq_complex_re] using (integral_re hHaar)
  rw [hRe, hComplex]
  rfl

end SpringerLean
