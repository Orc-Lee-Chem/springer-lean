import SpringerLean.Round18SignReduction

open MeasureTheory Set

namespace SpringerLean

/-- The first, purely measure-theoretic step of the centered-arc argument.
It applies to signed functions, not only nonnegative ones. The positive-part
integrability premise is explicit so this lemma works on arbitrary measures. -/
theorem setIntegral_le_threshold_add_positivePart
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (X : α → ℝ) (A : Set α) (hA : MeasurableSet A)
    (hX : Integrable X μ) (a : ℝ)
    (hPos : Integrable (fun x => max (X x - a) 0) μ) :
    (∫ x in A, X x ∂μ) ≤
      a * μ.real A + ∫ x, max (X x - a) 0 ∂μ := by
  let P : α → ℝ := fun x => max (X x - a) 0
  have hpoint (x : α) : X x ≤ a + P x := by
    dsimp [P]
    have h := le_max_left (X x - a) 0
    linarith
  have hconst : IntegrableOn (fun _ : α => a) A μ := by
    exact integrableOn_const
  have hsum : IntegrableOn (fun x => a + P x) A μ := hconst.add hPos.restrict
  have hfirst := setIntegral_mono_on hX.restrict hsum hA (fun x _ => hpoint x)
  have hsecond : (∫ x in A, P x ∂μ) ≤ ∫ x, P x ∂μ := by
    have hnonneg : 0 ≤ᵐ[μ.restrict Set.univ] P := by
      filter_upwards with x
      exact le_max_right _ _
    have hsub : A ≤ᵐ[μ] (Set.univ : Set α) := by
      filter_upwards with x
      intro _
      trivial
    have hPos' : IntegrableOn P Set.univ μ := by
      simpa [IntegrableOn, P] using hPos
    simpa only [setIntegral_univ] using
      (setIntegral_mono_set (f := P) (s := A) (t := Set.univ)
        hPos' hnonneg hsub)
  have hadd : (∫ x in A, a + P x ∂μ) =
      a * μ.real A + ∫ x in A, P x ∂μ := by
    rw [integral_add hconst hPos.restrict, setIntegral_const]
    simp [P, smul_eq_mul, mul_comm]
  rw [hadd] at hfirst
  linarith

end SpringerLean
