import SpringerLean.AnnulusFrontier

open Complex
open scoped ComplexConjugate

namespace SpringerLean

/-- The real directional projection of the corrected map is the real part
of a holomorphic scalar multiple of `F`. -/
theorem exteriorLinearCorrection_directional_re
    (F : ℂ → ℂ) (R : ℝ) (ξ w : ℂ) :
    (star ξ * exteriorLinearCorrection F R w).re =
      ((star ξ - ξ * star (exteriorForwardCoeff F 1 / (R : ℂ) ^ 2)) * w).re := by
  let c : ℂ := exteriorForwardCoeff F 1 / (R : ℂ) ^ 2
  have hstar : star (star ξ * c * star w) = ξ * star c * w := by
    simp only [star_mul, star_star]
    ring
  have hre : (star ξ * c * star w).re = (ξ * star c * w).re := by
    calc
      _ = (star (star ξ * c * star w)).re := by simp; ring
      _ = _ := congrArg Complex.re hstar
  change (star ξ * (w - c * star w)).re =
    ((star ξ - ξ * star c) * w).re
  simp only [mul_sub, sub_mul, Complex.sub_re, ← mul_assoc]
  rw [hre]

/-- Maximum modulus applied to `exp(αF)` transfers a uniform directional
bound from the two annulus boundaries to every interior point. -/
theorem exteriorLinearCorrection_directional_annulus_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R C : ℝ} (hr : 1 < r) (_hR : r < R)
    (hboundary : ∀ z : ℂ, (‖z‖ = r ∨ ‖z‖ = R) →
      ‖exteriorLinearCorrection F R (F z)‖ ≤ C)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) {z : ℂ}
    (hz : z ∈ exteriorAnnulus r R) :
    (star ξ * exteriorLinearCorrection F R (F z)).re ≤ C := by
  let c : ℂ := exteriorForwardCoeff F 1 / (R : ℂ) ^ 2
  let α : ℂ := star ξ - ξ * star c
  let G : ℂ → ℂ := fun w => Complex.exp (α * F w)
  have hcl : closure (exteriorAnnulus r R) ⊆ exteriorDisk :=
    exteriorAnnulus_closure_subset_exteriorDisk hr
  have hdiffF : DiffContOnCl ℂ F (exteriorAnnulus r R) :=
    (hc.1.mono hcl).diffContOnCl
  have hdiffG : DiffContOnCl ℂ G (exteriorAnnulus r R) := by
    have hd : Differentiable ℂ (fun w : ℂ => Complex.exp (α * w)) := by fun_prop
    exact hd.comp_diffContOnCl hdiffF
  have hbounded : Bornology.IsBounded (exteriorAnnulus r R) := by
    apply Metric.isBounded_ball.subset
    intro w hw
    change dist w 0 < R
    simpa only [dist_zero_right] using hw.2
  have hfront : ∀ w ∈ frontier (exteriorAnnulus r R), ‖G w‖ ≤ Real.exp C := by
    intro w hw
    have hwbound := hboundary w (exteriorAnnulus_frontier_radius r R hw)
    rw [show G w = Complex.exp (α * F w) by rfl, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (α * F w).re = (star ξ * exteriorLinearCorrection F R (F w)).re := by
        exact (exteriorLinearCorrection_directional_re F R ξ (F w)).symm
      _ ≤ ‖star ξ * exteriorLinearCorrection F R (F w)‖ := Complex.re_le_norm _
      _ = ‖exteriorLinearCorrection F R (F w)‖ := by
        rw [norm_mul, norm_star, hξ, one_mul]
      _ ≤ C := hwbound
  have hzG : ‖G z‖ ≤ Real.exp C :=
    norm_le_of_forall_mem_frontier_norm_le hbounded hdiffG hfront
      (subset_closure hz)
  rw [show G z = Complex.exp (α * F z) by rfl, Complex.norm_exp] at hzG
  have hreal : (α * F z).re ≤ C := Real.exp_le_exp.mp hzG
  rw [exteriorLinearCorrection_directional_re]
  exact hreal

/-- A real directional support bound in every unit direction gives the
ordinary complex norm bound. -/
private theorem norm_le_of_all_unit_directions
    (w : ℂ) (C : ℝ)
    (h : ∀ ξ : ℂ, ‖ξ‖ = 1 → (star ξ * w).re ≤ C) :
    ‖w‖ ≤ C := by
  by_cases hw : w = 0
  · subst w
    have hC := h 1 (by simp)
    simpa using hC
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    let ξ : ℂ := w / (‖w‖ : ℂ)
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hwpos, div_self hwpos.ne']
    have hdot : (star ξ * w).re = ‖w‖ := by
      have hnorm0 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      have hmul : star ξ * w = (‖w‖ : ℂ) := by
        dsimp [ξ]
        change star (w / (‖w‖ : ℂ)) * w = (‖w‖ : ℂ)
        rw [star_div₀,
          show star (‖w‖ : ℂ) = (‖w‖ : ℂ) by simp,
          div_mul_eq_mul_div]
        change (starRingEnd ℂ) w * w / (‖w‖ : ℂ) = (‖w‖ : ℂ)
        rw [Complex.conj_mul']
        field_simp [hnorm0]
      rw [hmul]
      simp
    rw [← hdot]
    exact h ξ hξ

/-- The corrected map, although only real-linear in its value argument,
obeys the same modulus bound throughout the annulus as on both circles. -/
theorem exteriorLinearCorrection_annulus_norm_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r R C : ℝ} (hr : 1 < r) (hR : r < R)
    (hboundary : ∀ z : ℂ, (‖z‖ = r ∨ ‖z‖ = R) →
      ‖exteriorLinearCorrection F R (F z)‖ ≤ C)
    {z : ℂ} (hz : z ∈ exteriorAnnulus r R) :
    ‖exteriorLinearCorrection F R (F z)‖ ≤ C := by
  apply norm_le_of_all_unit_directions
  intro ξ hξ
  exact exteriorLinearCorrection_directional_annulus_le
    F hc hr hR hboundary ξ hξ hz

/-- The fixed-constant corrected-image bound holds throughout every
sufficiently large exterior annulus. -/
theorem exteriorLinearCorrection_large_annulus_norm_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr : 1 < r) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ r < R₀ ∧
      ∀ (R : ℝ) (z : ℂ), R₀ ≤ R →
        z ∈ exteriorAnnulus r R →
          ‖exteriorLinearCorrection F R (F z)‖ ≤ R + C / R ^ 2 := by
  obtain ⟨C, R₁, hC, hR₁, hbound⟩ :=
    exteriorLinearCorrection_annulus_boundaries F hc hr
  let R₀ := max R₁ (r + 1)
  refine ⟨C, R₀, hC, ?_, ?_⟩
  · have := le_max_right R₁ (r + 1)
    dsimp [R₀]
    linarith
  intro R z hR hz
  have hR₁ : R₁ ≤ R := le_trans (le_max_left _ _) hR
  have hrR : r < R := by
    have := le_max_right R₁ (r + 1)
    dsimp [R₀] at hR
    linarith
  exact exteriorLinearCorrection_annulus_norm_le F hc hr hrR
    (fun w hw => hbound R w hR₁ hw) hz

end SpringerLean
