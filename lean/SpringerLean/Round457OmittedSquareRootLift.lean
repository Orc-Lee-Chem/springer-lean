import SpringerLean.Round456OmittedRootRadicand
import SpringerLean.TaylorBridge

namespace SpringerLean

noncomputable def omittedSquareRootLift (R : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * R ((z⁻¹) ^ 2)

theorem reciprocal_square_mem_unitBall {z : ℂ} (hz : z ∈ exteriorDisk) :
    (z⁻¹) ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
  have hz1 : 1 < ‖z‖ := hz
  have hz2 : 1 < ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hp : 0 < ‖z‖ ^ 2 := by linarith
  simpa only [Metric.mem_ball, dist_zero_right, norm_pow, norm_inv, inv_pow] using
    (inv_lt_one₀ hp).mpr hz2

theorem omittedSquareRootLift_odd (R : ℂ → ℂ) (z : ℂ) :
    omittedSquareRootLift R (-z) = -omittedSquareRootLift R z := by
  simp [omittedSquareRootLift]

theorem omittedSquareRootLift_square
    (F R : ℂ → ℂ) (P : ℂ)
    (hRpow : ∀ u ∈ Metric.ball (0 : ℂ) 1,
      R u ^ 2 = exteriorPhi F u - P * u)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    omittedSquareRootLift R z ^ 2 = F (z ^ 2) - P := by
  have hz0 := exterior_ne_zero hz
  have hu0 : (z⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hz0)
  have hf := exteriorF_reciprocal_phi F hu0
  simp only [inv_pow, inv_inv] at hf
  dsimp only [omittedSquareRootLift]
  rw [mul_pow, hRpow _ (reciprocal_square_mem_unitBall hz), hf]
  field_simp [hz0] <;> ring

theorem omittedSquareRootLift_forwardGerm
    (R : ℂ → ℂ) (hR0 : R 0 = 1) :
    exteriorForwardGerm (omittedSquareRootLift R) =
      fun u => u * dslope R 0 (u ^ 2) := by
  funext u
  by_cases hu : u = 0
  · subst u
    simp [exteriorForwardGerm_zero]
  rw [exteriorForwardGerm_punctured _ hu]
  dsimp only [omittedSquareRootLift]
  rw [inv_inv, analytic_dslope_decomposition R (u ^ 2), hR0]
  field_simp [hu] <;> ring

theorem omittedSquareRootLift_centeredExteriorUnivalent
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F)
    (R : ℂ → ℂ) (hRa : AnalyticOnNhd ℂ R (Metric.ball (0 : ℂ) 1))
    (hR0 : R 0 = 1)
    (hRpow : ∀ u ∈ Metric.ball (0 : ℂ) 1,
      R u ^ 2 = exteriorPhi F u - P * u) :
    CenteredExteriorUnivalent (omittedSquareRootLift R) := by
  have hsquare {z : ℂ} (hz : z ∈ exteriorDisk) :
      omittedSquareRootLift R z ^ 2 = F (z ^ 2) - P :=
    omittedSquareRootLift_square F R P hRpow hz
  have hsquaredDomain {z : ℂ} (hz : z ∈ exteriorDisk) : z ^ 2 ∈ exteriorDisk := by
    change 1 < ‖z ^ 2‖
    rw [norm_pow]
    have hz1 : 1 < ‖z‖ := hz
    nlinarith [norm_nonneg z]
  have hnonzero {z : ℂ} (hz : z ∈ exteriorDisk) : omittedSquareRootLift R z ≠ 0 := by
    intro he
    have hs := hsquare hz
    rw [he, zero_pow (by omega : (2 : ℕ) ≠ 0)] at hs
    have hF : F (z ^ 2) = P := sub_eq_zero.mp hs.symm
    exact hP ⟨z ^ 2, hsquaredDomain hz, hF⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hInv : AnalyticAt ℂ (fun w : ℂ => (w⁻¹) ^ 2) z := by
      convert (analyticAt_id.inv (exterior_ne_zero hz)).pow 2 using 1 <;> first | rfl | simp
    have hComp : AnalyticAt ℂ (fun w : ℂ => R ((w⁻¹) ^ 2)) z := by
      simpa only [Function.comp_def] using
        (hRa _ (reciprocal_square_mem_unitBall hz)).comp
          (f := fun w : ℂ => (w⁻¹) ^ 2) (x := z) hInv
    exact (analyticAt_id.mul hComp).differentiableAt.differentiableWithinAt
  · intro z hz w hw heq
    have hf : F (z ^ 2) = F (w ^ 2) := by
      have hs := congrArg (fun a : ℂ => a ^ 2) heq
      rw [hsquare hz, hsquare hw] at hs
      exact sub_left_inj.mp hs
    have hsq := hc.2.1 (hsquaredDomain hz) (hsquaredDomain hw) hf
    have hfactor : (z - w) * (z + w) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · exact sub_eq_zero.mp hleft
    · have hzneg : z = -w := eq_neg_iff_add_eq_zero.mpr hright
      rw [hzneg, omittedSquareRootLift_odd R w] at heq
      have hzero : omittedSquareRootLift R w = 0 := by
        linear_combination (-1 / 2 : ℂ) * heq
      exact False.elim (hnonzero hw hzero)
  · rw [omittedSquareRootLift_forwardGerm R hR0]
    have hds := analyticAt_dslope_zero R (hRa 0 (by simp))
    have hds' : AnalyticAt ℂ (dslope R 0) ((0 : ℂ) ^ 2) := by simpa using hds
    have hComp : AnalyticAt ℂ (fun u : ℂ => dslope R 0 (u ^ 2)) 0 := by
      simpa only [Function.comp_def] using hds'.comp
        (f := fun u : ℂ => u ^ 2) (x := 0) (analyticAt_id.pow 2)
    exact analyticAt_id.mul hComp

/-- Actual odd exterior square-root map, obtained from the original hypotheses. -/
theorem exteriorOmitted_exists_odd_squareRoot_map
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) :
    ∃ H : ℂ → ℂ, CenteredExteriorUnivalent H ∧
      (∀ z, H (-z) = -H z) ∧
      ∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - P := by
  obtain ⟨R, hRa, hR0, hRpow⟩ := exteriorOmitted_exists_normalized_analytic_root F hc hP
  exact ⟨omittedSquareRootLift R,
    omittedSquareRootLift_centeredExteriorUnivalent F hc hP R hRa hR0 hRpow,
    omittedSquareRootLift_odd R, fun z hz => omittedSquareRootLift_square F R P hRpow hz⟩

end SpringerLean
