import SpringerLean.Round28UniformCoercive

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- If a low-cost test set has strictly more mass than a threshold
candidate, the candidate's threshold cannot exceed that test level. -/
theorem threshold_le_of_large_bounded_test
    (f : ℝ → ℝ) (ell B : ℝ) (E J : Set ℝ)
    (hbelow : {t | f t < ell} ⊆ E)
    (hJbound : ∀ t ∈ J, f t ≤ B)
    (hEfin : volume E ≠ ∞)
    (hmass : volume.real E < volume.real J) : ell ≤ B := by
  by_contra hn
  have hBell : B < ell := lt_of_not_ge hn
  have hJE : J ⊆ E := by
    intro t ht
    exact hbelow (lt_of_le_of_lt (hJbound t ht) hBell)
  have hle : volume.real J ≤ volume.real E :=
    measureReal_mono hJE hEfin
  linarith

end SpringerLean