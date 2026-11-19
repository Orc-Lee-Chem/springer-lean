import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace SpringerLean

open Polynomial

/-- Clearing the denominator in w^n Q(w+a/w) leaves constant coefficient
a^n whenever Q is monic of degree n. This is the algebraic obstruction to
a polynomial lemniscate having a unit-slit exterior map. -/
noncomputable def clearedSlitPolynomial
    (n : ℕ) (a : ℂ) (b : ℕ → ℂ) : ℂ[X] :=
  ∑ i ∈ Finset.range (n + 1),
    C (b i) * X ^ (n - i) * (X ^ 2 + C a) ^ i

theorem clearedSlitPolynomial_eval_zero
    (n : ℕ) (a : ℂ) (b : ℕ → ℂ) (hmonic : b n = 1) :
    (clearedSlitPolynomial n a b).eval 0 = a ^ n := by
  unfold clearedSlitPolynomial
  rw [eval_finsetSum]
  have hs : (∑ i ∈ Finset.range (n + 1),
      eval 0 (C (b i) * X ^ (n - i) * (X ^ 2 + C a) ^ i)) =
      eval 0 (C (b n) * X ^ (n - n) * (X ^ 2 + C a) ^ n) := by
    apply Finset.sum_eq_single n
    · intro i hi hne
      have hlt : i < n := by
        have := Finset.mem_range.mp hi
        omega
      have hsub : n - i ≠ 0 := by omega
      simp [hsub]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  rw [hs]
  simp [hmonic]

theorem clearedSlitPolynomial_ne_purePower
    (n : ℕ) (hn : 0 < n) (a : ℂ) (ha : a ≠ 0)
    (b : ℕ → ℂ) (hmonic : b n = 1) :
    clearedSlitPolynomial n a b ≠ X ^ (2 * n) := by
  intro heq
  have hval := congrArg (fun P : ℂ[X] => P.eval 0) heq
  rw [clearedSlitPolynomial_eval_zero n a b hmonic] at hval
  have htwon : 2 * n ≠ 0 := by omega
  simp only [eval_pow, eval_X, zero_pow htwon] at hval
  exact (pow_ne_zero n ha) hval

theorem clearedSlitPolynomial_eval_eq
    (Q : ℂ[X]) (n : ℕ) (hn : Q.natDegree = n)
    (a w : ℂ) (hw : w ≠ 0) :
    (clearedSlitPolynomial n a Q.coeff).eval w =
      w ^ n * Q.eval (w + a / w) := by
  have hrewrite : w + a / w = (w ^ 2 + a) / w := by
    field_simp [hw]
  rw [Q.eval_eq_sum_range' (n := n + 1) (by omega) (w + a / w)]
  unfold clearedSlitPolynomial
  rw [eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ n := by have := Finset.mem_range.mp hi; omega
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add]
  rw [hrewrite]
  have hpow : w ^ n = w ^ (n - i) * w ^ i := by
    rw [← pow_add]
    congr 1
    omega
  rw [div_pow, hpow]
  field_simp [pow_ne_zero i hw]

/-- The algebraic strictness step for a general monic polynomial Q.
An identity Q(w+a/w)=w^n on the whole open exterior disk would already
contradict this theorem by polynomial identity on an infinite set. -/
theorem monicPolynomial_no_slit_identity
    (Q : ℂ[X]) (hQ : Q.Monic) (n : ℕ) (hn : Q.natDegree = n)
    (hn0 : 0 < n) (a : ℂ) (ha : a ≠ 0) :
    ¬ ∀ w : ℂ, w ≠ 0 → Q.eval (w + a / w) = w ^ n := by
  intro hid
  have hpoly : clearedSlitPolynomial n a Q.coeff = X ^ (2 * n) := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hnonzero : (Set.univ \ ({0} : Set ℂ)).Infinite :=
      Set.infinite_univ.sdiff (Set.finite_singleton 0)
    apply hnonzero.mono
    intro w hw
    have hw0 : w ≠ 0 := by simpa using hw
    change (clearedSlitPolynomial n a Q.coeff).eval w = (X ^ (2 * n) : ℂ[X]).eval w
    rw [clearedSlitPolynomial_eval_eq Q n hn a w hw0, hid w hw0]
    simp only [eval_pow, eval_X]
    rw [← pow_add]
    congr 1
    omega
  have hlead : Q.coeff n = 1 := by simpa only [← hn] using hQ.coeff_natDegree
  exact clearedSlitPolynomial_ne_purePower n hn0 a ha Q.coeff hlead hpoly

/-- This is the exact open-exterior-disk form needed for strictness in
the polynomial zero-moment theorem. -/
theorem monicPolynomial_no_exterior_slit_identity
    (Q : ℂ[X]) (hQ : Q.Monic) (n : ℕ) (hn : Q.natDegree = n)
    (hn0 : 0 < n) (a : ℂ) (ha : a ≠ 0) :
    ¬ ∀ w : ℂ, 1 < ‖w‖ → Q.eval (w + a / w) = w ^ n := by
  intro hid
  have hpoly : clearedSlitPolynomial n a Q.coeff = X ^ (2 * n) := by
    apply Polynomial.eq_of_infinite_eval_eq
    let f : ℕ → ℂ := fun j => ((j + 2 : ℕ) : ℂ)
    have hfinj : Function.Injective f := by
      intro i j hij
      dsimp [f] at hij
      exact Nat.add_right_cancel (by exact_mod_cast hij)
    have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hfinj
    apply hrange.mono
    intro w hw
    obtain ⟨j, rfl⟩ := hw
    have hnorm : 1 < ‖f j‖ := by
      dsimp [f]
      simp only [Complex.norm_natCast]
      exact_mod_cast (by omega : 1 < j + 2)
    have hw0 : f j ≠ 0 := by
      apply norm_ne_zero_iff.mp
      exact ne_of_gt (lt_trans zero_lt_one hnorm)
    change (clearedSlitPolynomial n a Q.coeff).eval (f j) =
      (X ^ (2 * n) : ℂ[X]).eval (f j)
    rw [clearedSlitPolynomial_eval_eq Q n hn a (f j) hw0, hid (f j) hnorm]
    simp only [eval_pow, eval_X]
    rw [← pow_add]
    congr 1
    omega
  have hlead : Q.coeff n = 1 := by simpa only [← hn] using hQ.coeff_natDegree
  exact clearedSlitPolynomial_ne_purePower n hn0 a ha Q.coeff hlead hpoly

end SpringerLean

#print axioms SpringerLean.clearedSlitPolynomial_ne_purePower
#print axioms SpringerLean.monicPolynomial_no_slit_identity
#print axioms SpringerLean.monicPolynomial_no_exterior_slit_identity
