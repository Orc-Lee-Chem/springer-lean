import SpringerLean.Round19ThresholdSet

open MeasureTheory Set

namespace SpringerLean

/-- The positive-part integral is exactly the excess of the integral on the
superlevel set over the threshold times that set's mass. -/
theorem integral_positivePart_eq_superlevel_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (a : ℝ)
    (hC : MeasurableSet {x | a ≤ X x})
    (hX : Integrable X μ)
    (hPos : Integrable (fun x => max (X x - a) 0) μ) :
    (∫ x, max (X x - a) 0 ∂μ) =
      (∫ x in {x | a ≤ X x}, X x ∂μ) -
        a * μ.real {x | a ≤ X x} := by
  let C : Set α := {x | a ≤ X x}
  let P : α → ℝ := fun x => max (X x - a) 0
  have hzero : (∫ x in Cᶜ, P x ∂μ) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxa : ¬ a ≤ X x := by
      simpa only [C, mem_compl_iff, mem_ofPred_eq] using hx
    dsimp [P]
    exact max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hxa)))
  have hsplit : (∫ x, P x ∂μ) = ∫ x in C, P x ∂μ := by
    have h := integral_add_compl (μ := μ) hC hPos
    rw [hzero, add_zero] at h
    exact h.symm
  have hwithin : (∫ x in C, P x ∂μ) = ∫ x in C, X x - a ∂μ := by
    apply setIntegral_congr_fun hC
    intro x hx
    dsimp [P, C] at *
    exact max_eq_left (sub_nonneg.mpr hx)
  rw [hsplit, hwithin, integral_sub hX.restrict integrableOn_const,
    setIntegral_const]
  simp [C, smul_eq_mul, mul_comm]

/-- Among measurable sets of a fixed measure, a superlevel set maximizes the
integral of a real integrable function. This keeps the function signed. -/
theorem setIntegral_le_superlevel_of_measure_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (A : Set α) (a : ℝ)
    (hA : MeasurableSet A)
    (hC : MeasurableSet {x | a ≤ X x})
    (hX : Integrable X μ)
    (hPos : Integrable (fun x => max (X x - a) 0) μ)
    (hmass : μ.real A = μ.real {x | a ≤ X x}) :
    (∫ x in A, X x ∂μ) ≤ ∫ x in {x | a ≤ X x}, X x ∂μ := by
  let C : Set α := {x | a ≤ X x}
  let P : α → ℝ := fun x => max (X x - a) 0
  have hzero : (∫ x in Cᶜ, P x ∂μ) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxa : ¬ a ≤ X x := by
      simpa only [C, mem_compl_iff, mem_ofPred_eq] using hx
    dsimp [P]
    exact max_eq_right (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hxa)))
  have hsplit : (∫ x, P x ∂μ) = ∫ x in C, P x ∂μ := by
    have h := integral_add_compl (μ := μ) hC hPos
    rw [hzero, add_zero] at h
    exact h.symm
  have hwithin : (∫ x in C, P x ∂μ) = ∫ x in C, X x - a ∂μ := by
    apply setIntegral_congr_fun hC
    intro x hx
    dsimp [P, C] at *
    exact max_eq_left (sub_nonneg.mpr hx)
  have hcalc : (∫ x in C, X x - a ∂μ) =
      (∫ x in C, X x ∂μ) - a * μ.real C := by
    rw [integral_sub hX.restrict integrableOn_const, setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hfirst := setIntegral_le_threshold_add_positivePart X A hA hX a hPos
  change (∫ x in A, X x ∂μ) ≤ a * μ.real A + ∫ x, P x ∂μ at hfirst
  rw [hsplit, hwithin, hcalc, hmass] at hfirst
  linarith

end SpringerLean
