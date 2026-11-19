import SpringerLean.Round14AreaCircle
import SpringerLean.Round14Quadratic
import SpringerLean.Round35SlitSharpness

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

theorem exteriorForwardGerm_mul_id_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun u : ℂ => u * exteriorForwardGerm F u) 0 r = 0 := by
  have hAnal : AnalyticOnNhd ℂ (fun u : ℂ => u * exteriorForwardGerm F u)
      (ball 0 1) := by
    intro u hu
    have hG := exteriorForwardGerm_analyticOnNhd_unitBall F hc u hu
    fun_prop
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro u hu
    rw [abs_of_nonneg hr0] at hu
    exact lt_of_le_of_lt hu hr1
  have hcont : ContinuousOn (fun u : ℂ => u * exteriorForwardGerm F u)
      (closedBall (0 : ℂ) |r|) := hAnal.continuousOn.mono hsub
  have hdiff : ∀ u ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun v : ℂ => v * exteriorForwardGerm F v) u := by
    intro u hu
    exact (hAnal u (hsub (ball_subset_closedBall hu.1))).differentiableAt
  simpa only [zero_mul] using
    (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff)

/-- The cross term of the actual harmonic filling has zero normalized
circle average. -/
theorem actualHarmonic_cross_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z : ℂ => ((conj z) * exteriorForwardGerm F (conj z)).re) 0 r = 0 := by
  let g := exteriorForwardGerm F
  have hclosed : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro z hz
    exact lt_of_le_of_lt hz hr1
  have hg : ContinuousOn g (closedBall (0 : ℂ) r) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.mono hclosed
  have hconj : ContinuousOn (fun z : ℂ => conj z) (closedBall (0 : ℂ) r) :=
    Complex.continuous_conj.continuousOn
  have hgconj : ContinuousOn (fun z : ℂ => g (conj z)) (closedBall (0 : ℂ) r) := by
    apply hg.comp hconj
    intro z hz
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
  have hcross : ContinuousOn (fun z : ℂ => conj z * g (conj z))
      (closedBall (0 : ℂ) r) := hconj.mul hgconj
  have hci : CircleIntegrable (fun z : ℂ => conj z * g (conj z)) 0 r :=
    (hcross.mono sphere_subset_closedBall).circleIntegrable hr0.le
  have hC : Real.circleAverage (fun z : ℂ => conj z * g (conj z)) 0 r = 0 := by
    rw [circleAverage_comp_conj_zero (fun z : ℂ => z * g z) r]
    exact exteriorForwardGerm_mul_id_circleAverage_zero F hc hr0.le hr1
  change Real.circleAverage
    (Complex.reCLM ∘ (fun z : ℂ => conj z * g (conj z))) 0 r = 0
  rw [Complex.reCLM.circleAverage_comp_comm hci, hC]
  simp
private theorem actualHarmonic_pointwise_energy (F : ℂ → ℂ) (z : ℂ) :
    ‖actualHarmonic F z‖ ^ 2 =
      ‖z‖ ^ 2 + ‖exteriorForwardGerm F (conj z)‖ ^ 2 +
        2 * ((conj z) * exteriorForwardGerm F (conj z)).re := by
  simp only [actualHarmonic, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
/-- The circle second moment of the actual harmonic filling is the radius
square plus the forward-correction circle energy. -/
theorem actualHarmonic_circle_energy_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) 0 r =
      r ^ 2 + Real.circleAverage
        (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) 0 r := by
  let g := exteriorForwardGerm F
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro z hz
    exact lt_of_le_of_lt hz hr1
  have hg : ContinuousOn g (closedBall (0 : ℂ) r) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.mono hsub
  have hconj : ContinuousOn (fun z : ℂ => conj z) (closedBall (0 : ℂ) r) :=
    Complex.continuous_conj.continuousOn
  have hgconj : ContinuousOn (fun z : ℂ => g (conj z))
      (closedBall (0 : ℂ) r) := by
    apply hg.comp hconj
    intro z hz
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using hz
  have hzcont : ContinuousOn (fun z : ℂ => z) (closedBall (0 : ℂ) r) :=
    continuous_id.continuousOn
  have hcrosscont : ContinuousOn
      (fun z : ℂ => ((conj z) * g (conj z)).re)
      (closedBall (0 : ℂ) r) :=
    Complex.continuous_re.comp_continuousOn (hconj.mul hgconj)
  have hzi : CircleIntegrable (fun z : ℂ => ‖z‖ ^ 2) 0 r :=
    (((hzcont.norm).pow 2).mono sphere_subset_closedBall).circleIntegrable hr0.le
  have hgi : CircleIntegrable (fun z : ℂ => ‖g (conj z)‖ ^ 2) 0 r :=
    (((hgconj.norm).pow 2).mono sphere_subset_closedBall).circleIntegrable hr0.le
  have hci : CircleIntegrable
      (fun z : ℂ => ((conj z) * g (conj z)).re) 0 r :=
    (hcrosscont.mono sphere_subset_closedBall).circleIntegrable hr0.le
  have h2ci : CircleIntegrable (fun z : ℂ =>
      2 * ((conj z) * g (conj z)).re) 0 r :=
    (((continuousOn_const.mul hcrosscont).mono sphere_subset_closedBall).circleIntegrable hr0.le)
  have hnormz :
      Real.circleAverage (fun z : ℂ => ‖z‖ ^ 2) 0 r = r ^ 2 := by
    calc
      Real.circleAverage (fun z : ℂ => ‖z‖ ^ 2) 0 r =
          Real.circleAverage (fun _ : ℂ => r ^ 2) 0 r := by
            apply Real.circleAverage_congr_sphere
            intro z hz
            have hzNorm : ‖z‖ = r := by
              simpa [mem_sphere, dist_zero_right, abs_of_pos hr0] using hz
            simp [hzNorm]
      _ = r ^ 2 := Real.circleAverage_const _ _ _
  calc
    Real.circleAverage (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) 0 r =
      Real.circleAverage
        (fun z : ℂ => ‖z‖ ^ 2 + ‖g (conj z)‖ ^ 2 +
          2 * ((conj z) * g (conj z)).re) 0 r := by
            congr 1
            funext z
            exact actualHarmonic_pointwise_energy F z
    _ = Real.circleAverage (fun z : ℂ => ‖z‖ ^ 2) 0 r +
          Real.circleAverage (fun z : ℂ => ‖g (conj z)‖ ^ 2) 0 r +
          2 * Real.circleAverage
            (fun z : ℂ => ((conj z) * g (conj z)).re) 0 r := by
            calc
              _ = Real.circleAverage
                    (fun z : ℂ => ‖z‖ ^ 2 + ‖g (conj z)‖ ^ 2) 0 r +
                  Real.circleAverage
                    (fun z : ℂ => 2 * ((conj z) * g (conj z)).re) 0 r :=
                    Real.circleAverage_fun_add (hzi.add hgi) h2ci
              _ = _ := by
                rw [Real.circleAverage_fun_add hzi hgi]
                simp only [← smul_eq_mul, Real.circleAverage_fun_smul]
    _ = r ^ 2 + Real.circleAverage (fun z : ℂ => ‖g z‖ ^ 2) 0 r := by
      rw [actualHarmonic_cross_circleAverage_zero F hc hr0 hr1,
        circleAverage_comp_conj_zero (fun z : ℂ => ‖g z‖ ^ 2) r,
        hnormz]
      ring
/-- The actual harmonic filling has circle second moment at most twice the
squared radius. -/
theorem actualHarmonic_circle_energy_le_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖actualHarmonic F z‖ ^ 2) 0 r
      ≤ 2 * r ^ 2 := by
  rw [actualHarmonic_circle_energy_eq F hc hr0 hr1]
  have h := exteriorForwardGerm_circle_energy_le F hc hr0 hr1
  linarith
/-- The real slit attains the actual filling circle second-moment bound. -/
theorem slitMap_one_actualHarmonic_circle_energy_eq_two
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z : ℂ => ‖actualHarmonic (slitMap 1) z‖ ^ 2) 0 r =
      2 * r ^ 2 := by
  have hfun :
      (fun z : ℂ => ‖actualHarmonic (slitMap 1) z‖ ^ 2) =
      (fun z : ℂ =>
        (Complex.re (conj (1 : ℂ) * actualHarmonic (slitMap 1) z)) ^ 2) := by
    funext z
    rw [slitMap_one_actualHarmonic_eq_two_re]
    simp [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_abs z.re]
  rw [hfun]
  exact slitMap_one_projection_quadratic_circleAverage_eq hr0 hr1
end SpringerLean
