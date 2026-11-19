import SpringerLean.Round26Universal

open MeasureTheory Set
open scoped Classical

namespace SpringerLean

/-- A pointwise equality of the sums of two indicator functions gives the
corresponding equality of real integrals. All four integrals are required
to be genuine integrals, so the result cannot use Lean's default value for
a nonintegrable function. -/
theorem setIntegral_pair_eq_of_indicator_count
    (f : ℝ → ℝ) (A B P Q : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hfA : IntegrableOn f A) (hfB : IntegrableOn f B)
    (hfP : IntegrableOn f P) (hfQ : IntegrableOn f Q)
    (hcount : ∀ t : ℝ,
      (if t ∈ A then (1 : ℕ) else 0) + (if t ∈ B then 1 else 0) =
      (if t ∈ P then 1 else 0) + (if t ∈ Q then 1 else 0)) :
    (∫ t in A, f t) + (∫ t in B, f t) =
      (∫ t in P, f t) + (∫ t in Q, f t) := by
  have hpoint : ∀ t : ℝ,
      A.indicator f t + B.indicator f t =
        P.indicator f t + Q.indicator f t := by
    intro t
    have hc :
        (if t ∈ A then (1 : ℝ) else 0) + (if t ∈ B then 1 else 0) =
        (if t ∈ P then 1 else 0) + (if t ∈ Q then 1 else 0) := by
      exact_mod_cast hcount t
    calc
      A.indicator f t + B.indicator f t =
          ((if t ∈ A then (1 : ℝ) else 0) +
            (if t ∈ B then 1 else 0)) * f t := by
              by_cases ha : t ∈ A <;> by_cases hb : t ∈ B <;>
                simp [Set.indicator, ha, hb] <;> ring
      _ = ((if t ∈ P then (1 : ℝ) else 0) +
            (if t ∈ Q then 1 else 0)) * f t := by rw [hc]
      _ = P.indicator f t + Q.indicator f t := by
            by_cases hp : t ∈ P <;> by_cases hq : t ∈ Q <;>
              simp [Set.indicator, hp, hq] <;> ring
  calc
    (∫ t in A, f t) + (∫ t in B, f t) =
        (∫ t, A.indicator f t) + (∫ t, B.indicator f t) := by
          rw [integral_indicator hA, integral_indicator hB]
    _ = ∫ t, A.indicator f t + B.indicator f t := by
          rw [integral_add (hfA.integrable_indicator hA)
            (hfB.integrable_indicator hB)]
    _ = ∫ t, P.indicator f t + Q.indicator f t := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = (∫ t, P.indicator f t) + (∫ t, Q.indicator f t) := by
          rw [integral_add (hfP.integrable_indicator hP)
            (hfQ.integrable_indicator hQ)]
    _ = (∫ t in P, f t) + (∫ t in Q, f t) := by
          rw [integral_indicator hP, integral_indicator hQ]

end SpringerLean
