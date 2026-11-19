import SpringerLean.Round682FiniteQuantile
import SpringerLean.Round19UpperLevel

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- An exact quantile is a genuine optimizer of the signed integral.
Both mass and maximality are proved; there is no assumed optimizer field.
The hypotheses are generic measure-theoretic inputs, to be discharged
for the actual angular projection before using this as a paper entry. -/
theorem finiteMeasure_exists_top_set
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hInt : Integrable f μ)
    (B : ℝ) (habove : ∀ x, f x ≤ B)
    (hlevels : ∀ c : ℝ, μ {x | f x = c} = 0)
    (m : ℝ≥0∞) (hmpos : 0 < m)
    (hmass : ∃ R : ℝ, m ≤ μ {x | -f x ≤ R}) :
    ∃ ell : ℝ, MeasurableSet {x | ell ≤ f x} ∧
      μ {x | ell ≤ f x} = m ∧
      ∀ A : Set α, MeasurableSet A → μ A = m →
        (∫ x in A, f x ∂μ) ≤ ∫ x in {x | ell ≤ f x}, f x ∂μ := by
  obtain ⟨ell, hstrict⟩ := finiteMeasure_exists_strict_superlevel_mass_eq
    μ f hf B habove hlevels m hmpos hmass
  have hne : ∀ᵐ x ∂μ, f x ≠ ell := by
    apply ae_iff.mpr
    simpa only [ne_eq, not_not] using hlevels ell
  have heq : {x | ell ≤ f x} =ᵐ[μ] {x | ell < f x} := by
    filter_upwards [hne] with x hx
    simp only [mem_setOf_eq, le_iff_lt_or_eq, Ne.symm hx, or_false]
  have hclosed : μ {x | ell ≤ f x} = m := (measure_congr heq).trans hstrict
  have hC : MeasurableSet {x | ell ≤ f x} := measurableSet_le measurable_const hf
  refine ⟨ell, hC, hclosed, ?_⟩
  intro A hA hAm
  have hPos : Integrable (fun x => max (f x - ell) 0) μ := by
    have hfun : (fun x => max (f x-ell) 0) =
        ((f-fun _ => ell) ⊔ fun _ => (0 : ℝ)) := by
      funext x
      exact le_antisymm (max_le le_sup_left le_sup_right)
        (sup_le (le_max_left _ _) (le_max_right _ _))
    rw [hfun]
    exact (hInt.sub (integrable_const ell)).sup (integrable_const (0 : ℝ))
  apply setIntegral_le_superlevel_of_measure_eq f A ell hA hC hInt hPos
  simp only [Measure.real_def, hAm, hclosed]

end SpringerLean
