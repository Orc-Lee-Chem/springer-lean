import SpringerLean.Round764ChebyshevInterlacing
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

namespace SpringerLean

open Polynomial

/-- A zero of the next derivative lies strictly between any two distinct
zeros of the current derivative. This is the induction step used to compare
higher Chebyshev derivative zeros with the original cosine grid. -/
theorem polynomial_iterated_derivative_zero_between
    (p : ℝ[X]) (j : ℕ) {x y : ℝ} (hxy : x < y)
    (hx : ((derivative^[j]) p).eval x = 0)
    (hy : ((derivative^[j]) p).eval y = 0) :
    ∃ z : ℝ, x < z ∧ z < y ∧ ((derivative^[j + 1]) p).eval z = 0 := by
  obtain ⟨z, hz, hderiv⟩ :=
    exists_deriv_eq_zero hxy (((derivative^[j]) p).continuousOn) (hx.trans hy.symm)
  refine ⟨z, hz.1, hz.2, ?_⟩
  rw [Polynomial.deriv] at hderiv
  simpa only [Function.iterate_succ_apply'] using hderiv

/-- Every real-rooted polynomial remains completely real-rooted after
one differentiation, with roots counted with multiplicity. -/
theorem real_rooted_derivative_of_real_rooted (p : ℝ[X])
    (hp : p.roots.card = p.natDegree) :
    p.derivative.roots.card = p.derivative.natDegree := by
  have hlo := p.card_roots_le_derivative
  have hhi := p.derivative.card_roots'
  rw [natDegree_derivative] at hhi ⊢
  by_cases hzero : p.natDegree = 0
  · rw [derivative_of_natDegree_zero hzero]
    simp
    omega
  · omega

/-- All iterated derivatives of a completely real-rooted polynomial have
the maximum possible number of real roots, including multiplicities. -/
theorem real_rooted_iterated_derivative_of_real_rooted (p : ℝ[X])
    (hp : p.roots.card = p.natDegree) (j : ℕ) :
    ((derivative^[j]) p).roots.card = ((derivative^[j]) p).natDegree := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using
        real_rooted_derivative_of_real_rooted ((derivative^[j]) p) ih

/-- Every derivative of `T_n` has exactly `n-j` real roots, counted with
multiplicity. This supplies the completeness half of the higher-derivative
zero comparison in Proposition 9.2. -/
theorem chebyshev_iterated_derivative_real_roots (n j : ℕ) :
    ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).roots.card = n - j := by
  have hinj : Set.InjOn
      (fun k : ℕ => Real.cos ((2 * k + 1) * Real.pi / (2 * n)))
      (Finset.range n) :=
    (Finset.range n).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup n)
  have hbase : (Chebyshev.T ℝ (n : ℤ)).roots.card =
      (Chebyshev.T ℝ (n : ℤ)).natDegree := by
    rw [Chebyshev.roots_T_real, Chebyshev.natDegree_T]
    simp only [Int.natAbs_natCast]
    change (Finset.image
      (fun k : ℕ => Real.cos ((2 * k + 1) * Real.pi / (2 * n)))
      (Finset.range n)).card = n
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hdegree (j : ℕ) :
      ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).natDegree = n - j := by
    induction j with
    | zero => simp [Chebyshev.natDegree_T]
    | succ j ih =>
        rw [Function.iterate_succ_apply', natDegree_derivative, ih]
        omega
  rw [real_rooted_iterated_derivative_of_real_rooted _ hbase j,
    hdegree]

end SpringerLean

#print axioms SpringerLean.polynomial_iterated_derivative_zero_between
#print axioms SpringerLean.real_rooted_iterated_derivative_of_real_rooted
#print axioms SpringerLean.chebyshev_iterated_derivative_real_roots
