import SpringerLean.Round1973AffineDerivativeRoots

open Polynomial

namespace SpringerLean

/-- Exact equality of the multiplicity-counted derivative-zero
power sums under the arbitrary polynomial affine normalization. -/
theorem polynomialAffineMonic_derivative_root_power_sum
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (j : ℕ) (p : ℝ) :
    ((((derivative^[j]) (polynomialAffineMonic P c r)).roots.map
      (fun z : ℂ => ‖z‖ ^ p)).sum) =
    ((((derivative^[j]) P).roots.map
      (fun w : ℂ => ‖(w - c) / (r : ℂ)‖ ^ p)).sum) := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hroots := polynomialAffineMonic_derivative_roots_map P hP c r hr j
  have h := congrArg (fun s : Multiset ℂ =>
    (s.map (fun w : ℂ => ‖(w - c) / (r : ℂ)‖ ^ p)).sum) hroots
  have hcancel (z : ℂ) :
      ‖(((r : ℂ) * z + c) - c) / (r : ℂ)‖ ^ p = ‖z‖ ^ p := by
    have heq : (((r : ℂ) * z + c) - c) / (r : ℂ) = z := by
      field_simp [hrc]
      ring
    rw [heq]
  simpa only [Multiset.map_map, Function.comp_def, hcancel] using h

/-- The corresponding normalized means agree for every derivative
order below the original degree. -/
theorem polynomialAffineMonic_derivative_root_power_mean
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (c : ℂ) (r : ℝ) (hr : r ≠ 0)
    (j : ℕ) (_hj : j < P.natDegree) (p : ℝ) :
    ((((derivative^[j]) (polynomialAffineMonic P c r)).roots.map
      (fun z : ℂ => ‖z‖ ^ p)).sum) /
        ((P.natDegree - j : ℕ) : ℝ) =
    ((((derivative^[j]) P).roots.map
      (fun w : ℂ => ‖(w - c) / (r : ℂ)‖ ^ p)).sum) /
        ((P.natDegree - j : ℕ) : ℝ) := by
  rw [polynomialAffineMonic_derivative_root_power_sum P hP c r hr j p]

/-- The exact zero-moment normalization from the original polynomial
and original positive level, with centroid and radius chosen as in
Proposition 9.2. All roots are counted by multiplicity. -/
theorem originalPolynomial_derivative_root_power_mean_normalization
    (P : ℂ[X]) (hP : 0 < P.natDegree)
    (t : ℝ) (ht : 0 < t)
    (j : ℕ) (hj : j < P.natDegree) (p : ℝ) :
    ((((derivative^[j])
      (polynomialAffineMonic P (polynomialZeroCentroid P)
        (polynomialLemniscateRadius P t))).roots.map
          (fun z : ℂ => ‖z‖ ^ p)).sum) /
        ((P.natDegree - j : ℕ) : ℝ) =
    ((((derivative^[j]) P).roots.map
      (fun w : ℂ =>
        ‖(w - polynomialZeroCentroid P) /
          (polynomialLemniscateRadius P t : ℂ)‖ ^ p)).sum) /
        ((P.natDegree - j : ℕ) : ℝ) := by
  have hr := (polynomialLemniscateRadius_pos_and_norm P hP t ht).1
  exact polynomialAffineMonic_derivative_root_power_mean P hP
    (polynomialZeroCentroid P) (polynomialLemniscateRadius P t)
    hr.ne' j hj p

end SpringerLean

#print axioms SpringerLean.polynomialAffineMonic_derivative_root_power_sum
#print axioms SpringerLean.polynomialAffineMonic_derivative_root_power_mean
#print axioms SpringerLean.originalPolynomial_derivative_root_power_mean_normalization
