import SpringerLean.Round27ActualPair

open MeasureTheory Set
open scoped Classical

namespace SpringerLean

/-- Translation of a real set integral across the project's negative
vertical shift. -/
theorem setIntegral_verticalShiftMinus
    (f : ℝ → ℝ) (E : Set ℝ) (hE : MeasurableSet E) (ε : ℝ) :
    (∫ t in verticalShiftMinus E ε, f t) =
      ∫ u in E, f (u - ε) := by
  let g : ℝ → ℝ := fun u => f (u - ε)
  calc
    (∫ t in verticalShiftMinus E ε, f t) =
        ∫ t, (verticalShiftMinus E ε).indicator f t :=
          (integral_indicator (verticalShiftMinus_measurable hE ε)).symm
    _ = ∫ t, E.indicator g (t + ε) := by
          congr 1
          funext t
          by_cases ht : t + ε ∈ E <;>
            simp [verticalShiftMinus, Set.indicator, g, ht]
    _ = ∫ u, E.indicator g u :=
          integral_add_right_eq_self (E.indicator g) ε
    _ = ∫ u in E, f (u - ε) := by
          simpa only [g] using (integral_indicator (f := g) hE)

/-- Translation of a real set integral across the project's positive
vertical shift. -/
theorem setIntegral_verticalShiftPlus
    (f : ℝ → ℝ) (E : Set ℝ) (hE : MeasurableSet E) (ε : ℝ) :
    (∫ t in verticalShiftPlus E ε, f t) =
      ∫ u in E, f (u + ε) := by
  let g : ℝ → ℝ := fun u => f (u + ε)
  calc
    (∫ t in verticalShiftPlus E ε, f t) =
        ∫ t, (verticalShiftPlus E ε).indicator f t :=
          (integral_indicator (verticalShiftPlus_measurable hE ε)).symm
    _ = ∫ t, E.indicator g (t - ε) := by
          congr 1
          funext t
          by_cases ht : t - ε ∈ E <;>
            simp [verticalShiftPlus, Set.indicator, g, ht]
    _ = ∫ u, E.indicator g u := by
          simpa only [sub_eq_add_neg] using
            (integral_add_right_eq_self (E.indicator g) (-ε))
    _ = ∫ u in E, f (u + ε) := by
          simpa only [g] using (integral_indicator (f := g) hE)

end SpringerLean
