import SpringerLean.Round13PoissonFill
import Mathlib.Analysis.Complex.JensenFormula

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Away from the actual regularized boundary curve, an omitted value
gives a zero-free potential factor on the closed unit disk. -/
theorem regularBoundaryPotential_ne_zero_closedDisk_of_omitted
    (F : ℂ → ℂ) {s : ℝ} (hs0 : 0 < s)
    {w : ℂ} (hw : w ∈ exteriorOmitted (rescaleExterior s F))
    (hboundary : w ∉ rescaleExterior s F '' sphere (0 : ℂ) 1)
    {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) 1) :
    regularBoundaryPotential s F w u ≠ 0 := by
  have hle : ‖u‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using hu
  by_cases hlt : ‖u‖ < 1
  · exact regularBoundaryPotential_ne_zero_of_omitted F hs0 hw hlt
  · have heq : ‖u‖ = 1 := le_antisymm hle (le_of_not_gt hlt)
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      norm_num at heq
    intro hq
    have hImage : w ∈ rescaleExterior s F '' sphere (0 : ℂ) 1 := by
      have hInv : u⁻¹ ∈ sphere (0 : ℂ) 1 := by
        simpa only [mem_sphere, dist_zero_right, norm_inv, heq, inv_one]
      refine ⟨u⁻¹, hInv, ?_⟩
      rw [regularBoundaryPotential_punctured F hs0 w hu0] at hq
      exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hu0)
    exact hboundary hImage

/-- The zero-free Jensen identity for the actual regularized omitted value.
The conclusion is about the actual analytic factor; identifying its boundary
norm with `‖G_s-w‖` is a separate step. -/
theorem regularBoundaryPotential_omitted_circleAverage_log_norm_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {w : ℂ} (hw : w ∈ exteriorOmitted (rescaleExterior s F))
    (hboundary : w ∉ rescaleExterior s F '' sphere (0 : ℂ) 1) :
    Real.circleAverage
      (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖)
      0 1 = 0 := by
  have hlarge : 1 < s⁻¹ := by
    have h := one_div_lt_one_div_of_lt hs0 hs1
    simpa only [one_div, inv_one] using h
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 s⁻¹ := by
    intro u hu
    exact lt_of_le_of_lt hu hlarge
  have hAnal : AnalyticOnNhd ℂ (regularBoundaryPotential s F w)
      (closedBall (0 : ℂ) 1) :=
    (regularBoundaryPotential_analyticOnNhd F hc hs0 w).mono hsub
  have hne : ∀ u ∈ closedBall (0 : ℂ) 1,
      regularBoundaryPotential s F w u ≠ 0 :=
    fun u hu => regularBoundaryPotential_ne_zero_closedDisk_of_omitted
      F hs0 hw hboundary hu
  have h := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
    (R := (1 : ℝ)) (c := (0 : ℂ))
    (g := regularBoundaryPotential s F w)
    (by simpa only [abs_one] using hAnal)
    (by simpa only [abs_one] using hne)
  simpa only [regularBoundaryPotential_zero, norm_one, Real.log_one] using h

/-- The boundary logarithmic potential of an omitted value is zero.
The boundary curve is the actual `rescaleExterior s F`, and the excluded
curve condition prevents a logarithmic singularity on the integration path. -/
theorem regularExterior_omitted_boundary_log_potential_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {w : ℂ} (hw : w ∈ exteriorOmitted (rescaleExterior s F))
    (hboundary : w ∉ rescaleExterior s F '' sphere (0 : ℂ) 1) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - w‖) 0 1 = 0 := by
  have hpoint (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1) :
      ‖regularBoundaryPotential s F w (conj ζ)‖ =
        ‖rescaleExterior s F ζ - w‖ := by
    have hnorm : ‖ζ‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hζ
    have hconj0 : conj ζ ≠ 0 := by
      intro h
      have hzero : ζ = 0 := by
        simpa only [map_eq_zero] using h
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
          change Real.log ‖rescaleExterior s F ζ - w‖ =
            Real.log ‖regularBoundaryPotential s F w (conj ζ)‖
          rw [hpoint ζ (by simpa only [abs_one] using hζ)]
    _ = Real.circleAverage
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖)
        0 1 :=
      circleAverage_comp_conj_zero
        (fun u : ℂ => Real.log ‖regularBoundaryPotential s F w u‖) 1
    _ = 0 := regularBoundaryPotential_omitted_circleAverage_log_norm_zero
      F hc hs0 hs1 hw hboundary

end SpringerLean
