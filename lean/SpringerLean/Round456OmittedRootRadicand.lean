import SpringerLean.Round450DiskSquareRoot
import SpringerLean.Round08Omitted

namespace SpringerLean

noncomputable def omittedRootRadicand (F : ℂ → ℂ) (P u : ℂ) : ℂ :=
  exteriorPhi F u - P * u

@[simp] theorem omittedRootRadicand_zero (F : ℂ → ℂ) (P : ℂ) :
    omittedRootRadicand F P 0 = 1 := by
  simp [omittedRootRadicand, exteriorPhi]

theorem omittedRootRadicand_analytic
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (P : ℂ) :
    AnalyticOnNhd ℂ (omittedRootRadicand F P) (Metric.ball (0 : ℂ) 1) := by
  intro u hu
  have hg := exteriorForwardGerm_analyticOnNhd_unitBall F hc u hu
  change AnalyticAt ℂ (fun v => 1 + v * exteriorForwardGerm F v - P * v) u
  exact (analyticAt_const.add (analyticAt_id.mul hg)).sub
    (analyticAt_const.mul analyticAt_id)

theorem omittedRootRadicand_ne_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) {u : ℂ} (hu : ‖u‖ < 1) :
    omittedRootRadicand F P u ≠ 0 := by
  by_cases hu0 : u = 0
  · simp [hu0]
  intro he
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hE : u⁻¹ ∈ exteriorDisk := by
    change 1 < ‖u⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ hn).mpr hu
  have hphi : exteriorPhi F u = P * u := sub_eq_zero.mp he
  have hF : F u⁻¹ = P := by
    rw [exteriorF_reciprocal_phi F hu0, hphi]
    field_simp [hu0]
  exact hP ⟨u⁻¹, hE, hF⟩

/-- The branch needed by br:strip is constructed from the SAME actual F and
an actual omitted point. It is not an assumption on the paper function class. -/
theorem exteriorOmitted_exists_normalized_analytic_root
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (Metric.ball (0 : ℂ) 1) ∧
      R 0 = 1 ∧ ∀ u ∈ Metric.ball (0 : ℂ) 1,
        R u ^ 2 = exteriorPhi F u - P * u := by
  exact analyticOnNhd_unitBall_exists_normalized_square_root
    (omittedRootRadicand F P) (omittedRootRadicand_analytic F hc P)
    (omittedRootRadicand_zero F P)
    (fun u hu => omittedRootRadicand_ne_zero F hc hP (by simpa using hu))

end SpringerLean
