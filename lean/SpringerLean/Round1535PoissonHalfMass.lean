import SpringerLean.Round1534PoissonPeakExactFormula

open MeasureTheory Set Metric

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The centered Poisson kernel has unit mass in the normalized circle
measure, proved by applying the Poisson formula to the constant one. -/
theorem centeredPoisson_circleAverage_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ => poissonKernel 0 (r:ℂ) ζ) 0 1 = 1 := by
  have hz : (r:ℂ) ∈ ball (0:ℂ) 1 := by
    simp [Metric.mem_ball,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hr0,hr1]
  have hnot : (r:ℂ) ∉ sphere (0:ℂ) 1 := by
    intro hs
    have heq : ‖(r:ℂ)‖=1 := by
      simpa [Metric.mem_sphere,dist_zero_right] using hs
    simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0] at heq
    linarith
  have hkernel : ContinuousOn (poissonKernel 0 (r:ℂ)) (sphere (0:ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simpa only [abs_one] using
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere
          (c:=(0:ℂ)) (w:=(r:ℂ)) (R:=(1:ℝ))
          (by simpa only [abs_one] using hnot)))
  have hci : CircleIntegrable
      (fun ζ : ℂ => (poissonKernel 0 (r:ℂ) ζ) • (1:ℂ)) 0 1 :=
    (hkernel.smul continuousOn_const).circleIntegrable (by norm_num)
  have hmean : Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 (r:ℂ) ζ) • (1:ℂ)) 0 1 = (1:ℂ) := by
    exact ((differentiable_const (1:ℂ) :
      Differentiable ℂ (fun _ : ℂ => (1:ℂ))).diffContOnCl
        (s:=ball (0:ℂ) 1)).circleAverage_poissonKernel_smul hz
  have hre := Complex.reCLM.circleAverage_comp_comm hci
  rw [hmean] at hre
  have hreal : Real.circleAverage
      (fun ζ : ℂ => (poissonKernel 0 (r:ℂ) ζ) * (1:ℝ)) 0 1 = 1 := by
    simpa [Function.comp_def,Complex.reCLM_apply,Complex.real_smul]
      using hre
  simpa using hreal

/-- Half of the raw Poisson kernel mass is π, with no hidden factor of
two in the centered-arc normalization. -/
theorem centeredPoisson_half_interval_mass
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ θ in (0:ℝ)..Real.pi,
      poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)) = Real.pi := by
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r:ℂ) (circleMap 0 1 θ)
  have hPc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hsym (θ : ℝ) : P (2*Real.pi-θ)=P θ := by
    dsimp [P]
    rw [poissonKernel_centered_cosine_formula hr0.le hr1,
      poissonKernel_centered_cosine_formula hr0.le hr1,
      Real.cos_two_pi_sub]
  have hright : (∫ θ in Real.pi..(2*Real.pi), P θ) =
      ∫ θ in (0:ℝ)..Real.pi, P θ := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f:=P) (a:=(0:ℝ)) (b:=Real.pi) (2*Real.pi)
    have hcomp' : (∫ θ in (0:ℝ)..Real.pi, P (2*Real.pi-θ)) =
        ∫ θ in Real.pi..(2*Real.pi), P θ := by
      convert hcomp using 1 <;> ring
    rw [←hcomp']
    simp_rw [hsym]
  have hfull : (∫ θ in (0:ℝ)..(2*Real.pi), P θ) =
      2*(∫ θ in (0:ℝ)..Real.pi, P θ) := by
    have hInt1 : IntervalIntegrable P volume 0 Real.pi :=
      hPc.intervalIntegrable _ _
    have hInt2 : IntervalIntegrable P volume Real.pi (2*Real.pi) :=
      hPc.intervalIntegrable _ _
    rw [←intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2,
      hright]
    ring
  have hmean := centeredPoisson_circleAverage_one hr0 hr1
  rw [circleAverage_eq_restrictedAngularIntegral] at hmean
  change (2*Real.pi)⁻¹ *
    (∫ θ : ℝ, P θ ∂(volume.restrict (Ioc (0:ℝ) (2*Real.pi)))) = 1 at hmean
  rw [←intervalIntegral.integral_of_le (by positivity :
      (0:ℝ) ≤ 2*Real.pi),hfull] at hmean
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp at hmean
  linarith

end SpringerLean

#print axioms SpringerLean.centeredPoisson_circleAverage_one
#print axioms SpringerLean.centeredPoisson_half_interval_mass
