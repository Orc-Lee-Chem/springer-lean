import SpringerLean.Round257AllOrderActualFaber
import SpringerLean.Round144SixFiniteEnergy

open scoped Topology

namespace SpringerLean

theorem faberFiniteSignedEnergy_split
    (N : ℕ) (c : ℕ → ℂ) :
    (∑ k ∈ Finset.range (2 * N + 1),
      ((N : ℝ) - k) * ‖c k‖ ^ 2) =
      (∑ k ∈ Finset.range N, ((N : ℝ) - k) * ‖c k‖ ^ 2) -
        ∑ j ∈ Finset.range N,
          ((j + 1 : ℕ) : ℝ) * ‖c (N + (j + 1))‖ ^ 2 := by
  rw [show 2 * N + 1 = (N + 1) + N by omega,
    Finset.sum_range_add, Finset.sum_range_succ]
  have htail :
      (∑ j ∈ Finset.range N,
        ((N : ℝ) - ((N + 1 + j : ℕ) : ℝ)) * ‖c (N + 1 + j)‖ ^ 2) =
      -(∑ j ∈ Finset.range N,
        ((j + 1 : ℕ) : ℝ) * ‖c (N + (j + 1))‖ ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show N + 1 + j = N + (j + 1) by omega]
    push_cast
    ring
  rw [htail]
  simp
  ring

/-- General analytic-factor form of the finite negative-frequency area
bound. The signed area premise is discharged for actual polynomial
images by the project's proved Green/change-of-variables theorem. -/
theorem analyticFactor_negative_energy_le
    (A : ℂ → ℂ) {R : ℝ} (hR : 1 < R)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 R)) (N : ℕ)
    (harea :
      let γ : ℝ → ℂ := fun θ =>
        fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
          A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
      0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im) :
    (∑ j ∈ Finset.range N,
      ((j + 1 : ℕ) : ℝ) * ‖actualTaylorCoeff A (N + (j + 1))‖ ^ 2) ≤
      ∑ k ∈ Finset.range N,
        ((N : ℝ) - k) * ‖actualTaylorCoeff A k‖ ^ 2 := by
  let γ : ℝ → ℂ := fun θ =>
    fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hnonneg : 0 ≤ I := harea
  have hlim : Filter.Tendsto
      (fun M : ℕ => Real.pi *
        (∑ k ∈ Finset.range (M + 1),
          ((N : ℝ) - k) * ‖actualTaylorCoeff A k‖ ^ 2))
      Filter.atTop (nhds I) := by
    have hfun :
        (fun M : ℕ => Real.pi *
          (∑ k ∈ Finset.range (M + 1),
            ((N : ℝ) - k) * ‖actualTaylorCoeff A k‖ ^ 2)) =
        (fun M : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
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
  let B : ℝ :=
    (∑ k ∈ Finset.range N, ((N : ℝ) - k) * ‖actualTaylorCoeff A k‖ ^ 2) -
      ∑ j ∈ Finset.range N,
        ((j + 1 : ℕ) : ℝ) * ‖actualTaylorCoeff A (N + (j + 1))‖ ^ 2
  have hupper : I ≤ Real.pi * B :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨2 * N, by
      intro M hM
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      have h := faberFiniteSignedEnergy_le_twice N M (actualTaylorCoeff A) hM
      rw [faberFiniteSignedEnergy_split] at h
      exact h⟩)
  have hB : 0 ≤ B := by nlinarith [Real.pi_pos]
  dsimp [B] at hB
  linarith

end SpringerLean
