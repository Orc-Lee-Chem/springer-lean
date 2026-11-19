import SpringerLean.Round1738ActualDiskPointwiseEnergyAE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open MeasureTheory intervalIntegral

namespace SpringerLean

/-- The one-dimensional integration step for a compactly supported
coordinate slice of a locally Lipschitz physical flux. It remains
valid when the slice crosses arbitrarily many spline knot points. -/
theorem integral_deriv_zero_of_lipschitz_slice
    (f : ℝ → ℝ) (a b : ℝ) (C : NNReal)
    (hf : LipschitzOnWith C f (Set.uIcc a b))
    (ha : f a = 0) (hb : f b = 0) :
    ∫ x in a..b, deriv f x = 0 := by
  rw [hf.absolutelyContinuousOnInterval.integral_deriv_eq_sub,
    ha, hb, sub_self]

/-- The horizontal iterated divergence integral vanishes if every
coordinate slice is Lipschitz and vanishes at the two edges. -/
theorem integral_horizontal_deriv_zero_of_lipschitz_slices
    (Jx : ℝ × ℝ → ℝ) (a b c d : ℝ) (C : NNReal)
    (hL : ∀ y ∈ Set.uIcc c d,
      LipschitzOnWith C (fun x => Jx (x, y)) (Set.uIcc a b))
    (ha : ∀ y ∈ Set.uIcc c d, Jx (a, y) = 0)
    (hb : ∀ y ∈ Set.uIcc c d, Jx (b, y) = 0) :
    ∫ y in c..d, (∫ x in a..b,
      deriv (fun s => Jx (s, y)) x) = 0 := by
  have heq : Set.EqOn
      (fun y => ∫ x in a..b, deriv (fun s => Jx (s, y)) x)
      (fun _ : ℝ => (0 : ℝ)) (Set.uIcc c d) := by
    intro y hy
    exact integral_deriv_zero_of_lipschitz_slice
      (fun s => Jx (s, y)) a b C (hL y hy) (ha y hy) (hb y hy)
  rw [intervalIntegral.integral_congr heq]
  simp

/-- The same slice theorem for the vertical coordinate. -/
theorem integral_vertical_deriv_zero_of_lipschitz_slices
    (Jy : ℝ × ℝ → ℝ) (a b c d : ℝ) (C : NNReal)
    (hL : ∀ x ∈ Set.uIcc a b,
      LipschitzOnWith C (fun y => Jy (x, y)) (Set.uIcc c d))
    (hc : ∀ x ∈ Set.uIcc a b, Jy (x, c) = 0)
    (hd : ∀ x ∈ Set.uIcc a b, Jy (x, d) = 0) :
    ∫ x in a..b, (∫ y in c..d,
      deriv (fun s => Jy (x, s)) y) = 0 := by
  exact integral_horizontal_deriv_zero_of_lipschitz_slices
    (fun p : ℝ × ℝ => Jy (p.2, p.1)) c d a b C hL hc hd

end SpringerLean

#print axioms SpringerLean.integral_deriv_zero_of_lipschitz_slice
#print axioms SpringerLean.integral_horizontal_deriv_zero_of_lipschitz_slices
#print axioms SpringerLean.integral_vertical_deriv_zero_of_lipschitz_slices
