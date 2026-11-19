import SpringerLean.Round604UnitDiskCoefficientEnergy

open MeasureTheory
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem nat_nonnegative_sum_le_Icc
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (hw : ∀ j, 0 ≤ w j) (s : Finset ℕ) :
    (∑ j ∈ s, w j) ≤ ∑ j ∈ Finset.Icc 1 (s.sup id), w j := by
  have hsub : s.erase 0 ⊆ Finset.Icc 1 (s.sup id) := by
    intro j hj
    obtain ⟨hj0,hjs⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, Finset.le_sup (f := id) hjs⟩
  calc
    _ = ∑ j ∈ s.erase 0, w j := (Finset.sum_erase s hw0).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)

theorem exteriorRootMidpoint_reciprocal_weighted_summable
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    Summable (fun j : ℕ => (j : ℝ) *
      ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2) := by
  let w : ℕ → ℝ := fun j => (j : ℝ) *
    ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2
  have hw : ∀ j, 0 ≤ w j := by intro j; dsimp [w]; positivity
  have hw0 : w 0 = 0 := by simp [w]
  have hq2 : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  apply summable_of_sum_le (c := 1 / ‖q‖ ^ 2) hw
  intro s
  refine (nat_nonnegative_sum_le_Icc w hw0 hw s).trans ?_
  have he := exteriorRootMidpoint_finite_reciprocal_energy H J hH hJ q hq hs (s.sup id)
  have hv0 : 0 ≤ ∑ j ∈ Finset.Icc 1 (s.sup id),
      (j : ℝ) * ‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    positivity
  change (∑ j ∈ Finset.Icc 1 (s.sup id), w j) ≤ 1 / ‖q‖ ^ 2
  apply (le_div_iff₀ hq2).mpr
  dsimp [w] at *
  nlinarith

theorem exteriorRootMidpoint_total_coefficient_energy
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    (∑' j : ℕ, (j : ℝ) * ‖exteriorForwardCoeff (exteriorRootMidpoint H J) j‖ ^ 2) +
      ‖q‖ ^ 2 * (∑' j : ℕ, (j : ℝ) *
        ‖exteriorReciprocalCoeff (exteriorRootMidpoint H J) j‖ ^ 2) ≤ 1 := by
  let V := exteriorRootMidpoint H J
  let wV : ℕ → ℝ := fun j => (j : ℝ) * ‖exteriorForwardCoeff V j‖ ^ 2
  let wR : ℕ → ℝ := fun j => (j : ℝ) * ‖exteriorReciprocalCoeff V j‖ ^ 2
  let w : ℕ → ℝ := fun j => wV j + ‖q‖ ^ 2 * wR j
  have hw : ∀ j, 0 ≤ w j := by intro j; dsimp [w,wV,wR]; positivity
  have hw0 : w 0 = 0 := by simp [w,wV,wR]
  have hbound : ∑' j : ℕ, w j ≤ 1 := by
    apply Real.tsum_le_of_sum_le hw
    intro s
    refine (nat_nonnegative_sum_le_Icc w hw0 hw s).trans ?_
    simpa only [w, wV, wR, V, Finset.sum_add_distrib, Finset.mul_sum] using
      exteriorRootMidpoint_finite_reciprocal_energy H J hH hJ q hq hs (s.sup id)
  have hV := exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ q hq hs
  have hvs : Summable wV := exteriorForwardCoeff_weighted_summable V hV
  have hrs : Summable wR := exteriorRootMidpoint_reciprocal_weighted_summable H J hH hJ q hq hs
  dsimp only [w] at hbound
  have he : (∑' j : ℕ, (wV j + ‖q‖ ^ 2 * wR j)) =
      (∑' j : ℕ, wV j) + ‖q‖ ^ 2 * (∑' j : ℕ, wR j) :=
    (hvs.hasSum.add (hrs.hasSum.mul_left (‖q‖ ^ 2))).tsum_eq
  rw [he] at hbound
  exact hbound

/-- An actual Dirichlet budget, with both derivatives taken before evaluation
at the conjugate disk point. No equality of Parseval sums is required. -/
theorem exteriorRootMidpoint_dirichlet_budget
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
      ‖deriv (exteriorForwardGerm (exteriorRootMidpoint H J)) (conj z)‖ ^ 2) +
      ‖q‖ ^ 2 * (Real.pi⁻¹ * (∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (exteriorReciprocalGerm (exteriorRootMidpoint H J)) (conj z)‖ ^ 2)) ≤ 1 := by
  let V := exteriorRootMidpoint H J
  have hV := exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ q hq hs
  have hnz : ∀ z ∈ exteriorDisk, V z ≠ 0 :=
    fun z hz => (exteriorRootMidpoint_recover_left H J q hq hs hz).1
  have hsum := exteriorRootMidpoint_reciprocal_weighted_summable H J hH hJ q hq hs
  have hR := (analytic_deriv_unitDisk_energy_le (exteriorReciprocalGerm V)
    (exteriorReciprocalGerm_analyticOnNhd_unitBall V hV hnz) hsum).2
  have hF := exteriorForwardGerm_deriv_energy_le_coeff_energy V hV
  exact (add_le_add hF (mul_le_mul_of_nonneg_left hR (sq_nonneg ‖q‖))).trans
    (exteriorRootMidpoint_total_coefficient_energy H J hH hJ q hq hs)

end SpringerLean
