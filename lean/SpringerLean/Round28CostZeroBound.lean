import SpringerLean.Round28AuxJoint

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- Uniform linear vanishing of the actual minimum cost at zero height
on a bounded horizontal interval. -/
theorem regularVerticalCosts_inf_small_height_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (a h : ℝ), |a| ≤ A → 0 ≤ h → h ≤ H →
        0 ≤ sInf (regularVerticalCosts F s ξ a h) ∧
        sInf (regularVerticalCosts F s ξ a h) ≤ 2 * M * h := by
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let M : ℝ := A + H + C + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro a h ha hh hhH
  let S : Set ℝ := Icc (-h) h
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hS : S ∈ verticalFeasible h := by
    simpa [S] using centered_interval_verticalFeasible h 0
  have hSfin : volume S ≠ ∞ := by rw [hS.2.2]; finiteness
  have hSreal : volume.real S = 2 * h := by
    rw [Measure.real_def, hS.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hupper (t : ℝ) (ht : t ∈ S) : f t ≤ M := by
    have htbound : |t| ≤ h := abs_le.mpr ht
    let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
    have hzbound : ‖ξ * z‖ ≤ A + H := by
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
    dsimp [f, M]
    linarith
  have hf := regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a h S hS
  have hInt : (∫ t in S, f t) ≤ M * (2 * h) := by
    have hle : (∫ t in S, f t) ≤ ∫ _t in S, M := by
      apply integral_mono_ae hf (integrableOn_const hSfin)
      exact (ae_restrict_iff' hS.1).2
        (Filter.Eventually.of_forall hupper)
    rw [setIntegral_const, hSreal] at hle
    simpa only [smul_eq_mul, mul_comm] using hle
  have hlow : 0 ≤ sInf (regularVerticalCosts F s ξ a h) := by
    apply le_csInf (regularVerticalCosts_nonempty F s ξ a h)
    rintro q ⟨E, hE, rfl⟩
    exact integral_nonneg (fun t =>
      regularExterior_rotated_boundary_potential_nonneg
        F hc hs0 hs1 ξ hξ ((a : ℂ) + (t : ℂ) * Complex.I))
  have hInfLe := regularVerticalCosts_sInf_le_centered_interval
    F hc hs0 hs1 ξ hξ a h 0
  have hInf : sInf (regularVerticalCosts F s ξ a h) ≤ ∫ t in S, f t := by
    simpa [S, f] using hInfLe
  exact ⟨hlow, by nlinarith [hInt]⟩
end SpringerLean