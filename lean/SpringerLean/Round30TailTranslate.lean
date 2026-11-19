import SpringerLean.Round30FiniteComplementMean

open MeasureTheory Set

namespace SpringerLean

/-- Translating an integrand on the complement of a symmetric interval is
exactly the same as translating the interval endpoints. -/
theorem integral_compl_Icc_comp_add_right
    (f : ℝ → ℝ) (T ε : ℝ) :
    (∫ t in (Icc (-T) T)ᶜ, f (t + ε)) =
      (∫ t in (Icc (-T + ε) (T + ε))ᶜ, f t) := by
  have hmem (t : ℝ) :
      t ∈ (Icc (-T) T)ᶜ ↔ t + ε ∈ (Icc (-T + ε) (T + ε))ᶜ := by
    simp only [mem_compl_iff, mem_Icc]
    constructor <;> intro h <;> contrapose! h <;> constructor <;> linarith [h.1, h.2]
  calc
    (∫ t in (Icc (-T) T)ᶜ, f (t + ε)) =
        ∫ t : ℝ, (Icc (-T) T)ᶜ.indicator (fun t => f (t + ε)) t :=
      (integral_indicator measurableSet_Icc.compl).symm
    _ = ∫ t : ℝ,
          (Icc (-T + ε) (T + ε))ᶜ.indicator f (t + ε) := by
      congr 1
      funext t
      by_cases ht : t ∈ (Icc (-T) T)ᶜ
      · have ht' := (hmem t).mp ht
        simp [Set.indicator, ht, ht']
      · have ht' : t + ε ∉ (Icc (-T + ε) (T + ε))ᶜ := by
          exact mt (hmem t).mpr ht
        simp [Set.indicator, ht, ht']
    _ = ∫ t : ℝ, (Icc (-T + ε) (T + ε))ᶜ.indicator f t :=
      integral_add_right_eq_self _ ε
    _ = (∫ t in (Icc (-T + ε) (T + ε))ᶜ, f t) :=
      integral_indicator measurableSet_Icc.compl

end SpringerLean