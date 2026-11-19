import SpringerLean.Round1992OddStarActualBoundaryRotation
import Mathlib.RingTheory.RootsOfUnity.Complex

open Polynomial

namespace SpringerLean

/-- The exact cyclic product over the m-th roots of unity, including
the degenerate center w = 0, expressed through the primitive complex
root exp(2πi/m). -/
theorem cyclic_power_difference_product
    (m : ℕ) (hm : 0 < m) (u w : ℂ) :
    ((Multiset.range m).map
      (fun j => u - (Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))) ^ j * w)).prod =
        u ^ m - w ^ m := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  let P : ℂ[X] := X ^ m - C (w ^ m)
  have hζ : IsPrimitiveRoot ζ m :=
    Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hm)
  have hroots : P.roots =
      (Multiset.range m).map (fun j => ζ ^ j * w) := by
    simpa only [P, nthRoots] using hζ.nthRoots_eq (show w ^ m = w ^ m from rfl)
  have hmonic : P.Monic := monic_X_pow_sub_C (w ^ m) (Nat.ne_of_gt hm)
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hprod := hsplits.eval_eq_prod_roots_of_monic hmonic u
  rw [hroots] at hprod
  simpa only [P, ζ, eval_sub, eval_pow, eval_X, eval_C, Multiset.map_map,
    Function.comp_def] using hprod.symm

private theorem log_norm_multiset_product
    (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ 0) :
    Real.log ‖s.prod‖ =
      (s.map (fun x => Real.log ‖x‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : a ≠ 0 := hs a (by simp)
      have htail : ∀ x ∈ s, x ≠ 0 := by
        intro x hx
        exact hs x (by simp [hx])
      have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (by
        intro hz
        exact htail 0 hz rfl)
      simp only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
        norm_mul]
      rw [Real.log_mul (norm_ne_zero_iff.mpr ha)
        (norm_ne_zero_iff.mpr hprod), ih htail]

/-- The cyclic power difference becomes a finite sum of ordinary
logarithmic distances when the two m-th powers are distinct. -/
theorem cyclic_power_difference_log_sum
    (m : ℕ) (hm : 0 < m) (u w : ℂ)
    (hpow : u ^ m ≠ w ^ m) :
    Real.log ‖u ^ m - w ^ m‖ =
      ((Multiset.range m).map (fun j =>
        Real.log ‖u -
          (Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))) ^ j * w‖)).sum := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hζ : IsPrimitiveRoot ζ m :=
    Complex.isPrimitiveRoot_exp m (Nat.ne_of_gt hm)
  have hfac (j : ℕ) : u - ζ ^ j * w ≠ 0 := by
    intro heq
    have hu : u = ζ ^ j * w := sub_eq_zero.mp heq
    apply hpow
    calc
      u ^ m = (ζ ^ j * w) ^ m := by rw [hu]
      _ = (ζ ^ m) ^ j * w ^ m := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring
      _ = w ^ m := by rw [hζ.pow_eq_one, one_pow, one_mul]
  let s : Multiset ℂ := (Multiset.range m).map (fun j => u - ζ ^ j * w)
  have hs : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hfac j
  have hlog := log_norm_multiset_product s hs
  have hprod := cyclic_power_difference_product m hm u w
  simpa only [s, ζ, Multiset.map_map, Function.comp_def, hprod] using hlog

end SpringerLean

#print axioms SpringerLean.cyclic_power_difference_product
#print axioms SpringerLean.cyclic_power_difference_log_sum
