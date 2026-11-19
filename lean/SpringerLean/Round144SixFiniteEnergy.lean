import SpringerLean.Round143FaberFiniteFourier

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- Frequencies past the first `N` negative modes make a nonpositive
contribution to the oriented boundary area. -/
theorem faberFiniteSignedEnergy_le_twice
    (N M : ℕ) (c : ℕ → ℂ) (hM : 2 * N ≤ M) :
    (∑ j ∈ Finset.range (M + 1),
      ((N : ℝ) - (j : ℝ)) * ‖c j‖ ^ 2) ≤
    ∑ j ∈ Finset.range (2 * N + 1),
      ((N : ℝ) - (j : ℝ)) * ‖c j‖ ^ 2 := by
  let f : ℕ → ℝ := fun j => ((N : ℝ) - (j : ℝ)) * ‖c j‖ ^ 2
  have htail : (∑ j ∈ Finset.Ico (2 * N + 1) (M + 1), f j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hjN : 2 * N + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    dsimp [f]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hjr : ((2 * N + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hjN
      push_cast at hjr
      linarith
    · positivity
  have hsplit := Finset.sum_range_add_sum_Ico f
    (show 2 * N + 1 ≤ M + 1 by omega)
  change (∑ j ∈ Finset.range (M + 1), f j) ≤
    ∑ j ∈ Finset.range (2 * N + 1), f j
  linarith

theorem sixthFaberFiniteSignedEnergy_le_firstSix
    (c : ℕ → ℂ) (M : ℕ) (hM : 12 ≤ M) :
    (∑ j ∈ Finset.range (M + 1),
      (6 - (j : ℝ)) * ‖c j‖ ^ 2) ≤
      6 * ‖c 0‖ ^ 2 + 5 * ‖c 1‖ ^ 2 +
        4 * ‖c 2‖ ^ 2 + 3 * ‖c 3‖ ^ 2 +
        2 * ‖c 4‖ ^ 2 + ‖c 5‖ ^ 2 -
        (‖c 7‖ ^ 2 + 2 * ‖c 8‖ ^ 2 +
          3 * ‖c 9‖ ^ 2 + 4 * ‖c 10‖ ^ 2 +
          5 * ‖c 11‖ ^ 2 + 6 * ‖c 12‖ ^ 2) := by
  have h := faberFiniteSignedEnergy_le_twice 6 M c (by omega)
  convert h using 1
  simp [Finset.sum_range_succ]
  ring

/-- Taylor truncations of the common sixth-order boundary factor converge
in the actual oriented integral. -/
theorem sixthFaberCombination_boundary_area_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    let A := sixthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆
    let γn : ℕ → ℝ → ℂ := fun M θ =>
      fourier 6 (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          actualTaylorCoeff A j *
            (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)
    let γ : ℝ → ℂ := fun θ =>
      fourier 6 (θ : AddCircle (2 * Real.pi)) *
        A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
    Filter.Tendsto
      (fun M => ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γn M θ).re * deriv (fun t => (γn M t).im) θ)
      Filter.atTop
      (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (γ θ).re * (deriv γ θ).im)) := by
  dsimp only
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  exact faberBoundaryFactor_oriented_integral_tendsto
    _ hR (sixthFaberCombinationFactor_analyticOnNhd
      F hc hs0 α₁ α₂ α₃ α₄ α₅ α₆) 6

/-- Nonnegative actual area controls six negative Fourier modes for an
arbitrary six-row Faber test. -/
theorem sixthFaberCombination_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    let A := sixthFaberCombinationFactor
      (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆
    ‖actualTaylorCoeff A 7‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 10‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 11‖ ^ 2 +
        6 * ‖actualTaylorCoeff A 12‖ ^ 2 ≤
      6 * ‖actualTaylorCoeff A 0‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 1‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 2‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 3‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 4‖ ^ 2 +
        ‖actualTaylorCoeff A 5‖ ^ 2 := by
  dsimp only
  let A := sixthFaberCombinationFactor
    (rescaleExterior s F) α₁ α₂ α₃ α₄ α₅ α₆
  let γ : ℝ → ℂ := fun θ =>
    fourier 6 (θ : AddCircle (2 * Real.pi)) *
      A (fourier (-1) (θ : AddCircle (2 * Real.pi)))
  let I : ℝ := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (γ θ).re * (deriv γ θ).im
  have hR : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hAdiff : Differentiable ℝ γ := by
    simpa only [γ, A] using
      (faberBoundaryFactor_differentiable A hR
        (sixthFaberCombinationFactor_analyticOnNhd
          F hc hs0 α₁ α₂ α₃ α₄ α₅ α₆) 6)
  have hIm (θ : ℝ) : deriv (fun t => (γ t).im) θ =
      (deriv γ θ).im := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        (hAdiff θ).hasDerivAt).deriv
  have hIeq : I = ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t => (γ t).im) θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    simpa only using congrArg (fun x : ℝ => (γ θ).re * x) (hIm θ).symm
  have hnonneg : 0 ≤ I := by
    rw [hIeq]
    simpa only [γ, A] using
      sixthFaberCombination_boundary_area_nonneg
        F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅ α₆
  have hlim : Filter.Tendsto
      (fun M => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (6 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2))
      Filter.atTop (nhds I) := by
    have hfun : (fun M : ℕ => Real.pi *
        (∑ j ∈ Finset.range (M + 1),
          (6 - (j : ℝ)) * ‖actualTaylorCoeff A j‖ ^ 2)) =
        (fun M : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (fourier 6 (θ : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              actualTaylorCoeff A j *
                (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
            deriv (fun t : ℝ =>
              (fourier 6 (t : AddCircle (2 * Real.pi)) *
                (∑ j ∈ Finset.range (M + 1),
                  actualTaylorCoeff A j *
                    (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) := by
      funext M
      simpa using
        (faberFiniteBoundary_oriented_area 6 (actualTaylorCoeff A) M).symm
    rw [hfun]
    exact sixthFaberCombination_boundary_area_tendsto
      F hc hs0 hs1 α₁ α₂ α₃ α₄ α₅ α₆
  let B : ℝ :=
    6 * ‖actualTaylorCoeff A 0‖ ^ 2 +
      5 * ‖actualTaylorCoeff A 1‖ ^ 2 +
      4 * ‖actualTaylorCoeff A 2‖ ^ 2 +
      3 * ‖actualTaylorCoeff A 3‖ ^ 2 +
      2 * ‖actualTaylorCoeff A 4‖ ^ 2 +
      ‖actualTaylorCoeff A 5‖ ^ 2 -
      (‖actualTaylorCoeff A 7‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 10‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 11‖ ^ 2 +
        6 * ‖actualTaylorCoeff A 12‖ ^ 2)
  have hupper : I ≤ Real.pi * B :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨12, by
      intro M hM
      exact mul_le_mul_of_nonneg_left
        (sixthFaberFiniteSignedEnergy_le_firstSix
          (actualTaylorCoeff A) M hM) Real.pi_pos.le⟩)
  have hB : 0 ≤ B := by
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  dsimp [B] at hB
  linarith

end SpringerLean
