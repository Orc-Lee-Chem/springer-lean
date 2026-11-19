import SpringerLean.Round259ActualPolynomialEnergy
import SpringerLean.Round14CircleLimit
import SpringerLean.Round13Mean

set_option maxHeartbeats 1000000

open MeasureTheory AddCircle Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Finite coefficient algebra behind the boundary radial-moment energy.
The coefficient is linear, 2-d/N, rather than Schober's squared weight. -/
theorem radialFinite_energy_plus_signed_le
    (N M : ℕ) (c : ℕ → ℂ) (hM : 2 * N ≤ M) :
    (N : ℝ) * (∑ j ∈ Finset.range (M + 1), ‖c j‖ ^ 2) +
      (∑ j ∈ Finset.range (M + 1), ((N : ℝ) - j) * ‖c j‖ ^ 2) ≤
        ∑ j ∈ Finset.range (2 * N), (2 * (N : ℝ) - j) * ‖c j‖ ^ 2 := by
  let f : ℕ → ℝ := fun j => (2 * (N : ℝ) - j) * ‖c j‖ ^ 2
  have htail : (∑ j ∈ Finset.Ico (2 * N) (M + 1), f j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hNj : 2 * N ≤ j := (Finset.mem_Ico.mp hj).1
    have hNjr : 2 * (N : ℝ) ≤ j := by exact_mod_cast hNj
    dsimp only [f]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show 2 * N ≤ M + 1 by omega)
  calc
    _ = ∑ j ∈ Finset.range (M + 1), f j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [f]
      ring
    _ ≤ ∑ j ∈ Finset.range (2 * N), f j := by linarith

/-- Parseval as an actual circle-average limit for an analytic function
on a disk larger than the closed unit disk. -/
theorem analyticFactor_unitCircle_energy_tendsto
    (A : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 R)) :
    Tendsto
      (fun M => ∑ j ∈ Finset.range M, ‖actualTaylorCoeff A j‖ ^ 2)
      atTop (nhds (Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1)) := by
  let point := exteriorCirclePoint 1
  have hpcont : Continuous point := by
    unfold point exteriorCirclePoint
    fun_prop
  have hpnorm (θ : AddCircle (2 * Real.pi)) : ‖point θ‖ = 1 :=
    exteriorCirclePoint_norm (by norm_num) θ
  have hMap : Set.univ ⊆ point ⁻¹' Metric.closedBall (0 : ℂ) 1 := by
    intro θ hθ
    change dist (point θ) 0 ≤ 1
    rw [dist_zero_right, hpnorm]
  have hu := ((analytic_actualTaylor_uniform_closedUnitDisk A hR hA).comp point).mono hMap
  let p : ℕ → AddCircle (2 * Real.pi) → ℂ := fun M θ =>
    ∑ j ∈ Finset.range M, actualTaylorCoeff A j * point θ ^ j
  let q : AddCircle (2 * Real.pi) → ℂ := fun θ => A (point θ)
  have hp : ∀ M, Continuous (p M) := by
    intro M
    dsimp only [p]
    fun_prop
  have hq : Continuous q := by
    apply hA.continuousOn.comp_continuous hpcont
    intro θ
    simpa only [Metric.mem_ball, dist_zero_right, hpnorm] using hR
  have hlim := circle_energy_tendsto_of_uniform p q hp hq hu
  have hfinite (M : ℕ) :
      (∫ θ : AddCircle (2 * Real.pi), ‖p M θ‖ ^ 2 ∂haarAddCircle) =
        ∑ j ∈ Finset.range M, ‖actualTaylorCoeff A j‖ ^ 2 := by
    calc
      _ = Real.circleAverage
          (fun z : ℂ => ‖∑ j ∈ Finset.range M, actualTaylorCoeff A j * z ^ j‖ ^ 2) 0 1 :=
        (circleAverage_eq_haar_circle _ 1).symm
      _ = _ := by
        simpa only [one_pow, mul_one] using
          finiteTaylor_circleAverage_energy (actualTaylorCoeff A) 1 (by norm_num) M
  have hactual :
      (∫ θ : AddCircle (2 * Real.pi), ‖q θ‖ ^ 2 ∂haarAddCircle) =
        Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1 := by
    change (∫ θ : AddCircle (2 * Real.pi),
      ‖A (exteriorCirclePoint 1 θ)‖ ^ 2 ∂haarAddCircle) = _
    exact (circleAverage_eq_haar_circle (fun z : ℂ => ‖A z‖ ^ 2) 1).symm
  simpa only [hfinite, hactual] using hlim

/-- The complete signed coefficient energy, before discarding any tail,
converges to the actual oriented Green circulation. -/
theorem analyticFactor_unitCircle_signed_energy_tendsto
    (A : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 R)) (N : ℕ) :
    let γ : ℝ → ℂ := fun θ => fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
    Tendsto
      (fun M => Real.pi * ∑ j ∈ Finset.range (M + 1),
        ((N : ℝ) - j) * ‖actualTaylorCoeff A j‖ ^ 2)
      atTop (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  dsimp only
  have hfun :
      (fun M => Real.pi * ∑ j ∈ Finset.range (M + 1),
        ((N : ℝ) - j) * ‖actualTaylorCoeff A j‖ ^ 2) =
      (fun M => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
          (∑ j ∈ Finset.range (M + 1), actualTaylorCoeff A j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
          deriv (fun t : ℝ =>
            (fourier (N : ℤ) (t : AddCircle (2 * Real.pi)) *
              (∑ j ∈ Finset.range (M + 1), actualTaylorCoeff A j *
                (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) := by
    funext M
    simpa using (faberFiniteBoundary_oriented_area N (actualTaylorCoeff A) M).symm
  rw [hfun]
  exact faberBoundaryFactor_oriented_integral_tendsto A hR hA (N : ℤ)

/-- Generic analytic-factor consequence of nonnegative signed area. This
is an explicit development lemma; the area premise is discharged from the
original actual exterior class in the public theorem below. -/
theorem analyticFactor_circle_energy_le_radialFiniteEnergy
    (A : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 R)) (N : ℕ) (hN : 1 ≤ N)
    (harea :
      let γ : ℝ → ℂ := fun θ => fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
      0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (γ θ).re * (deriv γ θ).im) :
    Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1 ≤
      ∑ j ∈ Finset.range (2 * N),
        (2 - (j : ℝ) / (N : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2 := by
  let γ : ℝ → ℂ := fun θ => fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
    A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I := ∫ θ in (0 : ℝ)..(2 * Real.pi), (γ θ).re * (deriv γ θ).im
  let E := ∑ j ∈ Finset.range (2 * N),
    (2 * (N : ℝ) - j) * ‖actualTaylorCoeff A j‖ ^ 2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hT := (analyticFactor_unitCircle_energy_tendsto A hR hA).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hS := analyticFactor_unitCircle_signed_energy_tendsto A hR hA N
  have hlim := (hT.const_mul (Real.pi * N)).add hS
  have hupper : Real.pi * N *
      Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1 + I ≤ Real.pi * E := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop (2 * N)] with M hM
    have h := mul_le_mul_of_nonneg_left
      (radialFinite_energy_plus_signed_le N M (actualTaylorCoeff A) hM) Real.pi_pos.le
    simpa only [Function.comp_def, mul_add, mul_assoc, E] using h
  have hnonneg : 0 ≤ I := harea
  have hNE : (N : ℝ) * Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1 ≤ E := by
    apply le_of_mul_le_mul_left _ Real.pi_pos
    calc
      Real.pi * ((N : ℝ) * Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1) ≤
          Real.pi * ((N : ℝ) * Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1) + I :=
        le_add_of_nonneg_right hnonneg
      _ ≤ Real.pi * E := by simpa only [mul_assoc] using hupper
  have hdivide : Real.circleAverage (fun z : ℂ => ‖A z‖ ^ 2) 0 1 ≤ E / N :=
    (le_div_iff₀ hNpos).2 (by simpa only [mul_comm] using hNE)
  have hE : E / N = ∑ j ∈ Finset.range (2 * N),
      (2 - (j : ℝ) / (N : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2 := by
    dsimp only [E]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [ne_of_gt hNpos] <;> ring
  exact hdivide.trans_eq hE

/-- The regularized even boundary moment of the same actual F is bounded
by the finite forward energy from paper equation (rad-area). No radial
trace, prescribed area identity or extra boundary hypothesis is assumed. -/
theorem rescaleExterior_even_boundary_moment_le_finite_energy
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) (hm : 1 ≤ m) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ (2 * m)) 0 1 ≤
      ∑ d ∈ Finset.range (2 * m), (2 - (d : ℝ) / (m : ℝ)) *
        ‖PowerSeries.coeff d
          (formalExteriorPhi (exteriorFormalForward (rescaleExterior s F)) ^ m)‖ ^ 2 := by
  let G := rescaleExterior s F
  let A : ℂ → ℂ := fun u => exteriorPhi G u ^ m
  have hG : CenteredExteriorUnivalent G := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hA : AnalyticOnNhd ℂ A (Metric.ball 0 s⁻¹) := by
    intro u hu
    exact (rescaleExterior_phi_analyticOnNhd F hc hs0 u hu).pow m
  let γ : ℝ → ℂ := fun θ => fourier (m : ℤ) (θ : AddCircle (2 * Real.pi)) *
    A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  have hboundary (θ : ℝ) : G (greenPolar 1 θ) ^ m = γ θ := by
    have hnorm : ‖fourier (-1) (θ : AddCircle (2 * Real.pi))‖ = 1 := by
      rw [fourier_apply, Circle.norm_coe]
    have hu : fourier (-1) (θ : AddCircle (2 * Real.pi)) ≠ 0 := by
      intro hz
      simpa [hz] using hnorm
    have h := exteriorF_pow_reciprocal_phi G hu m
    simpa only [fourier_neg_one_inv, fourier_one_pow, greenPolar_one_eq_fourier, A, γ] using h
  have hdiff : Differentiable ℝ γ := faberBoundaryFactor_differentiable A hR hA (m : ℤ)
  have hIm (θ : ℝ) : deriv (fun t => (γ t).im) θ = (deriv γ θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hdiff θ).hasDerivAt).deriv
  have harea : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (γ θ).re * (deriv γ θ).im := by
    have h := faberPolynomial_actual_exterior_boundary_area_nonneg F hc hs0 hs1
      (Polynomial.X ^ m)
    have hboundary' (θ : ℝ) : rescaleExterior s F (greenPolar 1 θ) ^ m = γ θ :=
      hboundary θ
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
    simp_rw [hboundary'] at h
    simpa only [hIm] using h
  have hfinite := analyticFactor_circle_energy_le_radialFiniteEnergy A hR hA m hm harea
  have hcoeff (d : ℕ) : actualTaylorCoeff A d = PowerSeries.coeff d
      (formalExteriorPhi (exteriorFormalForward G) ^ m) := by
    have h := congrArg (PowerSeries.coeff d) (exteriorPhi_pow_actualTaylorSeries G hG m)
    simpa only [actualTaylorSeries_coeff, A] using h
  simp_rw [hcoeff] at hfinite
  have hcircle : Real.circleAverage (fun ζ : ℂ => ‖G ζ‖ ^ (2 * m)) 0 1 =
      Real.circleAverage (fun u : ℂ => ‖A u‖ ^ 2) 0 1 := by
    calc
      _ = Real.circleAverage (fun ζ : ℂ => ‖A (conj ζ)‖ ^ 2) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro ζ hζ
        have hnorm : ‖ζ‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using hζ
        have hζ0 : ζ ≠ 0 := by intro hz; simpa [hz] using hnorm
        have hconj : (conj ζ)⁻¹ = ζ := by rw [← Complex.inv_eq_conj hnorm, inv_inv]
        have h := exteriorF_reciprocal_phi G (u := conj ζ) (by simp [hζ0])
        rw [hconj] at h
        change ‖G ζ‖ ^ (2 * m) = ‖A (conj ζ)‖ ^ 2
        rw [h, norm_mul, hnorm, one_mul]
        simp only [A, norm_pow]
        rw [← pow_mul]
        congr 1
        omega
      _ = _ := circleAverage_comp_conj_zero (fun u : ℂ => ‖A u‖ ^ 2) 1
  rw [hcircle]
  exact hfinite

end SpringerLean
