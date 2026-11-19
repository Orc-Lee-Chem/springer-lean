import SpringerLean.Round28MassAdjust

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean

/-- The actual minimized vertical cost is monotone and locally Lipschitz
in positive height, uniformly over a bounded horizontal parameter set. -/
theorem regularVerticalCosts_inf_height_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (a h h' : ℝ), |a| ≤ A → 0 < h → h ≤ h' → h' ≤ H →
        0 ≤ sInf (regularVerticalCosts F s ξ a h') -
          sInf (regularVerticalCosts F s ξ a h) ∧
        sInf (regularVerticalCosts F s ξ a h') -
          sInf (regularVerticalCosts F s ξ a h) ≤ 2 * M * (h' - h) := by
  obtain ⟨T₀, hT₀0, hmin⟩ :=
    regularVerticalCosts_exists_minimizer_uniform_window
      F hc hs0 hs1 ξ hξ A H hA hH
  let T : ℝ := max T₀ (H + 1)
  have hT₀T : T₀ ≤ T := le_max_left _ _
  have hHT : H + 1 ≤ T := le_max_right _ _
  have hT0 : 0 ≤ T := le_trans hT₀0 hT₀T
  let J : Set ℝ := Icc (-T) T
  have hJfin : volume J ≠ ∞ := (isBounded_Icc (-T) T).measure_lt_top.ne
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let M : ℝ := A + T + C + 1
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hpotbound (a : ℝ) (ha : |a| ≤ A) (t : ℝ) (ht : t ∈ J) :
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ M := by
    have htab : |t| ≤ T := abs_le.mpr (by simpa only [J, mem_Icc] using ht)
    let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
    have hzbound : ‖ξ * z‖ ≤ A + T := by
      rw [norm_mul, hξ, one_mul]
      have htri : ‖z‖ ≤ |a| + |t| := by
        dsimp [z]
        calc
          ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤
            ‖(a : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |a| + |t| := by simp
      linarith
    have hpot := hC (ξ * z)
    rw [← regularExterior_rotated_potential_eq F s ξ hξ z] at hpot
    dsimp [M]
    linarith
  refine ⟨M, hM0, ?_⟩
  intro a h h' ha hh hhh' hh'H
  have hh'T : h' ≤ T := by linarith
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  let m : ℝ → ℝ := fun x => sInf (regularVerticalCosts F s ξ a x)
  have hnonneg (t : ℝ) : 0 ≤ f t :=
    regularExterior_rotated_boundary_potential_nonneg F hc hs0 hs1 ξ hξ _
  obtain ⟨E, hE, hET₀, hEq⟩ := hmin a h ha hh (hhh'.trans hh'H)
  have hET : E ⊆ J := by
    intro t ht
    have h := hET₀ ht
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  obtain ⟨D, hD, hED, hDJ⟩ :=
    verticalFeasible_extend_inside_Icc T h h' hT0 hh.le hhh' hh'T E hE hET
  have hEInt := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ a h E hE
  have hDInt := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ a h' D hD
  have hDfin : volume D ≠ ∞ := by rw [hD.2.2]; finiteness
  have hDreal : volume.real D = 2 * h' := by
    rw [Measure.real_def, hD.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hEreal : volume.real E = 2 * h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hDeltaMass : volume.real (D \ E) = 2 * (h' - h) := by
    rw [measureReal_sdiff hED hE.1 hDfin, hDreal, hEreal]
    ring
  have hDmin : m h' ≤ ∫ t in D, f t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h')
    exact ⟨D, hD, rfl⟩
  have hsplit : (∫ t in D \ E, f t) = (∫ t in D, f t) - ∫ t in E, f t :=
    setIntegral_sdiff hE.1 hDInt hED
  have hDdiffInt : IntegrableOn f (D \ E) := hDInt.mono_set diff_subset
  have hDbound : (∫ t in D \ E, f t) ≤ M * (2 * (h' - h)) := by
    have hDdiffFin : volume (D \ E) ≠ ∞ :=
      (hD.2.1.subset diff_subset).measure_lt_top.ne
    have hupper : (∫ t in D \ E, f t) ≤ ∫ _t in D \ E, M := by
      apply integral_mono_ae hDdiffInt (integrableOn_const hDdiffFin)
      exact (ae_restrict_iff' (hD.1.diff hE.1)).2
        (Filter.Eventually.of_forall (fun t ht => hpotbound a ha t (hDJ ht.1)))
    rw [setIntegral_const, hDeltaMass] at hupper
    simpa only [smul_eq_mul, mul_comm] using hupper
  have hUpper : m h' - m h ≤ 2 * M * (h' - h) := by
    dsimp [m] at hEq ⊢
    have h1 : (∫ t in D, f t) - (∫ t in E, f t) ≤
        M * (2 * (h' - h)) := by rwa [hsplit] at hDbound
    linarith [hDmin]
  obtain ⟨Elarge, hElarge, hElargeT, hEqLarge⟩ :=
    hmin a h' ha (lt_of_lt_of_le hh hhh') hh'H
  obtain ⟨Dsmall, hDsmall, hDsmallE⟩ :=
    verticalFeasible_shrink h' h hh.le hhh' Elarge hElarge
  have hElargeInt := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ a h' Elarge hElarge
  have hSmallInt := regularExterior_vertical_cost_integrableOn
    F hc hs0 hs1 ξ hξ a h Dsmall hDsmall
  have hSmallCost : m h ≤ ∫ t in Dsmall, f t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
    exact ⟨Dsmall, hDsmall, rfl⟩
  have hSmallLe : (∫ t in Dsmall, f t) ≤ ∫ t in Elarge, f t := by
    apply setIntegral_mono_set hElargeInt
      (Filter.Eventually.of_forall hnonneg) (Filter.Eventually.of_forall hDsmallE)
  have hLower : 0 ≤ m h' - m h := by
    dsimp [m] at hEq ⊢
    linarith [hSmallCost, hSmallLe, hEqLarge]
  exact ⟨hLower, by nlinarith [hUpper]⟩

end SpringerLean