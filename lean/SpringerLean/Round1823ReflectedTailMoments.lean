import SpringerLean.Round1821ExponentialTailMoments
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 600000

theorem reflected_Ioi_indicator (f : ℝ → ℝ) (c : ℝ) :
    (fun x => (Ioi (0 : ℝ)).indicator f (c-x))=
      (Iio c).indicator (fun x => f (c-x)) := by
  funext x
  by_cases hx : x < c
  · have hy : 0 < c-x := by linarith
    simp only [Set.indicator_of_mem (show c-x ∈ Ioi 0 from hy),
      Set.indicator_of_mem (show x ∈ Iio c from hx)]
  · have hy : ¬ 0 < c-x := by linarith
    simp only [Set.indicator_of_notMem (show c-x ∉ Ioi 0 from hy),
      Set.indicator_of_notMem (show x ∉ Iio c from hx)]

theorem integral_reflected_Iio (f : ℝ → ℝ) (c : ℝ) :
    (∫ x in Iio c, f (c-x))=∫ t in Ioi 0, f t := by
  have hh := integral_sub_left_eq_self ((Ioi (0 : ℝ)).indicator f) volume c
  rw [reflected_Ioi_indicator,integral_indicator measurableSet_Iio,
    integral_indicator measurableSet_Ioi] at hh
  exact hh

theorem integrableOn_reflected_Iio (f : ℝ → ℝ) (c : ℝ)
    (hf : IntegrableOn f (Ioi 0)) : IntegrableOn (fun x => f (c-x)) (Iio c) := by
  have hh : Integrable ((Ioi (0 : ℝ)).indicator f) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hcomp := hh.comp_sub_left c
  rw [reflected_Ioi_indicator,integrable_indicator_iff measurableSet_Iio] at hcomp
  exact hcomp

theorem reflected_exponential_tail_moments (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ x in Iio c, (c-x)*Real.exp (-(σ*(c-x))))=1/σ^2 ∧
    (∫ x in Iio c, (c-x)^2*Real.exp (-(σ*(c-x))))=2/σ^3 := by
  constructor
  · rw [integral_reflected_Iio (fun t => t*Real.exp (-(σ*t))) c]
    exact exponential_tail_first_moment hσ
  · rw [integral_reflected_Iio (fun t => t^2*Real.exp (-(σ*t))) c]
    exact exponential_tail_second_moment hσ

end SpringerLean

#print axioms SpringerLean.reflected_exponential_tail_moments
