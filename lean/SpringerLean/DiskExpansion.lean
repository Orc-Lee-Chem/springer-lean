import SpringerLean.AreaConsequences
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open scoped Topology

namespace SpringerLean

/-- The actual normalized forward correction is analytic throughout |u|<1,
not only in a neighborhood of the origin. -/
theorem exteriorForwardGerm_analyticOnNhd_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    AnalyticOnNhd ℂ (exteriorForwardGerm F) (Metric.ball 0 1) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact hc.2.2
  · have hsmall : ‖u‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hext : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt hpos hsmall
      simpa only [one_div, inv_one] using h
    have hF : AnalyticAt ℂ F u⁻¹ :=
      hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hext)
    have hinv : AnalyticAt ℂ (fun v : ℂ => v⁻¹) u :=
      analyticAt_inv hu0
    have hcomp : AnalyticAt ℂ (fun v : ℂ => F v⁻¹) u := by
      simpa only [Function.comp_def] using hF.comp hinv
    have hlocal :
        exteriorForwardGerm F =ᶠ[𝓝 u]
          (fun v : ℂ => F v⁻¹ - v⁻¹) := by
      have hne : ∀ᶠ v : ℂ in 𝓝 u, v ≠ 0 := by
        simpa only [id_eq] using (continuousAt_id.eventually_ne hu0)
      filter_upwards [hne] with v hv
      simp [exteriorForwardGerm, hv]
    exact (hcomp.sub hinv).congr hlocal.symm

theorem exteriorForwardGerm_differentiableOn_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    DifferentiableOn ℂ (exteriorForwardGerm F) (Metric.ball 0 1) :=
  (exteriorForwardGerm_analyticOnNhd_unitBall F hc).differentiableOn

/-- The derivative-defined b_j represent the same actual correction at every
point of the open unit disk. -/
theorem exteriorForwardGerm_hasSum_coeff_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ => exteriorForwardCoeff F j * u ^ j)
      (exteriorForwardGerm F u) := by
  have hu' : u ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hs := Complex.hasSum_taylorSeries_on_ball
    (exteriorForwardGerm_differentiableOn_unitBall F hc) hu'
  simpa [exteriorForwardCoeff, smul_eq_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hs

/-- The actual derivative has its expected convergent mode expansion on the
entire unit disk; these are the coefficients needed for finite Fourier Bessel. -/
theorem exteriorForwardGerm_deriv_hasSum_coeff_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum
      (fun j : ℕ => (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * u ^ j)
      (deriv (exteriorForwardGerm F) u) := by
  have hu' : u ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hderiv :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.differentiableOn
  have hs := Complex.hasSum_taylorSeries_on_ball hderiv hu'
  have hcoef (j : ℕ) :
      (↑j.factorial : ℂ)⁻¹ *
          iteratedDeriv j (deriv (exteriorForwardGerm F)) 0 =
        (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) := by
    simpa [actualTaylorCoeff, exteriorForwardCoeff,
      div_eq_mul_inv, mul_comm] using
      (actualTaylorCoeff_deriv (exteriorForwardGerm F) j)
  have hterm (j : ℕ) :
      (↑j.factorial : ℂ)⁻¹ • (u - 0) ^ j •
          iteratedDeriv j (deriv (exteriorForwardGerm F)) 0 =
        (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * u ^ j := by
    simp only [sub_zero, smul_eq_mul]
    calc
      (↑j.factorial : ℂ)⁻¹ *
          (u ^ j * iteratedDeriv j (deriv (exteriorForwardGerm F)) 0) =
        ((↑j.factorial : ℂ)⁻¹ *
          iteratedDeriv j (deriv (exteriorForwardGerm F)) 0) * u ^ j := by ring
      _ = _ := by rw [hcoef]
  simpa only [hterm] using hs

/-- On the actual exterior domain the derivative of F is read from the
derivative of the forward germ at the reciprocal point. -/
theorem exterior_deriv_eq_forwardGerm_deriv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    deriv F z = 1 - (z ^ 2)⁻¹ * deriv (exteriorForwardGerm F) z⁻¹ := by
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  have hu : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hz
    simpa only [one_div, inv_one] using h
  have hu' : z⁻¹ ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hf : DifferentiableAt ℂ (exteriorForwardGerm F) z⁻¹ :=
    ((exteriorForwardGerm_analyticOnNhd_unitBall F hc) z⁻¹ hu').differentiableAt
  have hderiv : HasDerivAt
      (fun v : ℂ => v + exteriorForwardGerm F v⁻¹)
      (1 - (z ^ 2)⁻¹ * deriv (exteriorForwardGerm F) z⁻¹) z := by
    have hsum := (hasDerivAt_id z).add
      (hf.hasDerivAt.comp z (hasDerivAt_inv hz0))
    convert hsum using 1
    · funext v
      rfl
    · ring
  have hlocal : F =ᶠ[𝓝 z]
      (fun v : ℂ => v + exteriorForwardGerm F v⁻¹) := by
    have hne : ∀ᶠ v : ℂ in 𝓝 z, v ≠ 0 := by
      simpa only [id_eq] using (continuousAt_id.eventually_ne hz0)
    filter_upwards [hne] with v hv
    have hfv := exteriorForwardGerm_punctured F (inv_ne_zero hv)
    rw [inv_inv] at hfv
    simpa only [inv_inv] using (eq_add_of_sub_eq' hfv.symm)
  rw [hlocal.deriv_eq, hderiv.deriv]

/-- Convergent negative-frequency expansion of the derivative of the actual
exterior map. The `j`-th term is the mode `-(j+2)`. -/
theorem exterior_deriv_hasSum_negative_modes
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    HasSum
      (fun j : ℕ => (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) *
        (z⁻¹) ^ (j + 2))
      (1 - deriv F z) := by
  have hu : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hz
    simpa only [one_div, inv_one] using h
  have hs := (exteriorForwardGerm_deriv_hasSum_coeff_unitBall F hc hu).mul_left
    (z ^ 2)⁻¹
  convert hs using 1
  · funext j
    simp only [inv_pow, pow_add, pow_two]
    ring
  · rw [exterior_deriv_eq_forwardGerm_deriv F hc hz]
    ring

end SpringerLean
