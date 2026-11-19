import SpringerLean.Round14JensenBoundary

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The regularized potential factor is analytic on a neighborhood of the
entire closed unit disk, uniformly for every target value. -/
theorem regularBoundaryPotential_analytic_closedDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ) :
    AnalyticOnNhd ℂ (regularBoundaryPotential s F w)
      (closedBall (0 : ℂ) 1) := by
  have hlarge : 1 < s⁻¹ := by
    have h := one_div_lt_one_div_of_lt hs0 hs1
    simpa only [one_div, inv_one] using h
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
    intro u hu
    exact lt_of_le_of_lt hu hlarge
  exact (regularBoundaryPotential_analyticOnNhd F hc hs0 w).mono hsub

/-- On the actual boundary curve, the analytic factor and the exterior
map difference have the same norm after angular reflection. -/
theorem regularExterior_boundary_log_potential_eq_factor
    (F : ℂ → ℂ) {s : ℝ} (hs0 : 0 < s) (w : ℂ) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 =
    Real.circleAverage
      (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖) 0 1 := by
  have hpoint (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) :
      ‖regularBoundaryPotential s F w (conj ζ)‖ =
        ‖rescaleExterior s F ζ - w‖ := by
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hconj0 : conj ζ ≠ 0 := by
      intro h
      have hzero : ζ = 0 := by simpa only [map_eq_zero] using h
      subst ζ
      norm_num at hnorm
    have hinv : (conj ζ)⁻¹ = ζ := by
      rw [Complex.inv_eq_conj (by simpa only [Complex.norm_conj] using hnorm)]
      simp
    rw [regularBoundaryPotential_punctured F hs0 w hconj0, hinv,
      norm_mul, Complex.norm_conj, hnorm, one_mul]
  calc
    Real.circleAverage
        (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 =
      Real.circleAverage
        (fun ζ : ℂ => Real.log ‖regularBoundaryPotential s F w (conj ζ)‖)
        0 1 := by
          apply Real.circleAverage_congr_sphere
          intro ζ hζ
          exact (congrArg Real.log (hpoint ζ (by simpa only [abs_one] using hζ))).symm
    _ = Real.circleAverage
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖) 0 1 :=
      circleAverage_comp_conj_zero
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖) 1

/-- The actual boundary logarithmic potential is zero for every omitted
value, including values lying on the regularized boundary curve. -/
theorem regularExterior_omitted_boundary_log_potential_zero_all
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {w : ℂ} (hw : w ∈ exteriorOmitted (rescaleExterior s F)) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 = 0 := by
  have hJ := circleAverage_log_norm_of_no_openDisk_zeros
    (regularBoundaryPotential s F w)
    (regularBoundaryPotential_analytic_closedDisk F hc hs0 hs1 w)
    (by simp)
    (fun u hu => regularBoundaryPotential_ne_zero_of_omitted F hs0 hw hu)
  calc
    _ = Real.circleAverage
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖) 0 1 :=
      regularExterior_boundary_log_potential_eq_factor F hs0 w
    _ = Real.log ‖regularBoundaryPotential s F w 0‖ := hJ
    _ = 0 := by simp

/-- A value attained on the actual regularized unit-circle boundary has
zero logarithmic boundary potential, with its boundary zero handled by Jensen. -/
theorem regularExterior_curve_boundary_log_potential_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : ‖v‖ = 1) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = 0 := by
  have hJ := circleAverage_log_norm_of_no_openDisk_zeros
    (regularBoundaryPotential s F (rescaleExterior s F v))
    (regularBoundaryPotential_analytic_closedDisk F hc hs0 hs1 _)
    (by simp)
    (fun u hu => regularBoundaryPotential_ne_zero_openDisk_of_boundary F hc hs0 hs1 hv hu)
  calc
    _ = Real.circleAverage
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F
          (rescaleExterior s F v) u‖) 0 1 :=
      regularExterior_boundary_log_potential_eq_factor F hs0 _
    _ = Real.log ‖regularBoundaryPotential s F (rescaleExterior s F v) 0‖ := hJ
    _ = 0 := by simp

/-- The logarithmic singularities of the actual regularized boundary
curve are integrable for every target value. -/
theorem regularExterior_boundary_log_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (w : ℂ) :
    CircleIntegrable (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖)
      0 1 := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hAnal : AnalyticOnNhd ℂ
      (fun ζ : ℂ => rescaleExterior s F ζ - w) (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hext : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hext).sub analyticAt_const
  have hMer : MeromorphicOn (fun ζ : ℂ => rescaleExterior s F ζ - w)
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hAnal.meromorphicOn
  exact hMer.circleIntegrable_log_norm

end SpringerLean