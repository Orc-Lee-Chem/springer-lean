import SpringerLean.Slit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.RingTheory.RootsOfUnity.Complex

open Polynomial Set

namespace SpringerLean

/-- If an actual exterior map satisfies the polynomial identity, its
rotated values exhaust the polynomial fiber, with multiplicities. -/
theorem polynomial_exterior_fiber_roots
    (Q : ℂ[X]) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : Set.InjOn F exteriorDisk)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (w : ℂ) (hw : w ∈ exteriorDisk) :
    let n := Q.natDegree
    let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
    (Q - C (w ^ n)).roots =
      Finset.univ.val.map (fun j : Fin n => F (w * ζ ^ (j : ℕ))) := by
  classical
  let n := Q.natDegree
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  let f : Fin n → ℂ := fun j => F (w * ζ ^ (j : ℕ))
  have hn : 0 < n := hdeg
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hn.ne'
  have hmem (j : Fin n) : w * ζ ^ (j : ℕ) ∈ exteriorDisk := by
    change 1 < ‖w * ζ ^ (j : ℕ)‖
    rwa [norm_mul, norm_pow, hζnorm, one_pow, mul_one]
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hζ.pow_inj i.isLt j.isLt
    exact mul_left_cancel₀ (exterior_ne_zero hw) (hF (hmem i) (hmem j) hij)
  have hroot (j : Fin n) : (Q - C (w ^ n)).eval (f j) = 0 := by
    rw [eval_sub, eval_C, hidentity _ (hmem j), mul_pow, ← pow_mul,
      Nat.mul_comm (j : ℕ) n, pow_mul, hζ.pow_eq_one, one_pow, mul_one, sub_self]
  have hdegree : (Q - C (w ^ n)).natDegree = n := natDegree_sub_C
  have hnonzero : Q - C (w ^ n) ≠ 0 := by
    intro heq
    rw [heq, natDegree_zero] at hdegree
    exact hn.ne' hdegree.symm
  let S : Finset ℂ := Finset.univ.map ⟨f, hinj⟩
  have hS : (Q - C (w ^ n)).roots = S.val := by
    apply roots_eq_of_natDegree_le_card_of_ne_zero _ _ hnonzero
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
      exact hroot j
    · simpa only [S, Finset.card_map, Finset.card_univ, Fintype.card_fin] using hdegree.le
  exact hS

/-- The polynomial identity and injectivity already force the entire
omitted set to be the closed unit lemniscate. -/
theorem polynomial_exterior_image_eq
    (Q : ℂ[X]) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : Set.InjOn F exteriorDisk)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree) :
    F '' exteriorDisk = {z : ℂ | 1 < ‖Q.eval z‖} := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    change 1 < ‖Q.eval (F w)‖
    rw [hidentity w hw, norm_pow]
    exact one_lt_pow₀ hw hdeg.ne'
  · intro hx
    change 1 < ‖Q.eval x‖ at hx
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval x) hdeg
    have hwext : w ∈ exteriorDisk := by
      change 1 < ‖w‖
      by_contra! h
      have hpow : ‖w‖ ^ Q.natDegree ≤ 1 := pow_le_one₀ (norm_nonneg _) h
      rw [← norm_pow, hw] at hpow
      exact (not_lt_of_ge hpow) hx
    have hroots := polynomial_exterior_fiber_roots Q hdeg F hF hidentity w hwext
    dsimp at hroots
    have hne : Q - C (Q.eval x) ≠ 0 := by
      intro heq
      have hd := natDegree_sub_C (p := Q) (a := Q.eval x)
      rw [heq, natDegree_zero] at hd
      exact hdeg.ne' hd.symm
    have hxroot : x ∈ (Q - C (Q.eval x)).roots := by
      apply (mem_roots hne).2
      simp [IsRoot.def]
    rw [← hw, hroots] at hxroot
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hxroot
    refine ⟨_, ?_, rfl⟩
    change 1 < ‖w * _ ^ (j : ℕ)‖
    have hζ := Complex.isPrimitiveRoot_exp Q.natDegree hdeg.ne'
    have hζnorm := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hdeg.ne'
    rwa [norm_mul, norm_pow, hζnorm, one_pow, mul_one]

/-- Explicit angle parametrization of all (n) roots above the circle
of radius `ρ^n`. Each appears once because the exterior branches are
distinct. -/
theorem polynomial_outer_circle_fiber_roots
    (Q : ℂ[X]) (hdeg : 0 < Q.natDegree)
    (F : ℂ → ℂ) (hF : Set.InjOn F exteriorDisk)
    (hidentity : ∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)
    (ρ θ : ℝ) (hρ : 1 < ρ) :
    let n := Q.natDegree
    (Q - C (circleMap 0 (ρ ^ n) θ)).roots =
      Finset.univ.val.map (fun j : Fin n =>
        F (circleMap 0 ρ ((θ + 2 * Real.pi * (j : ℕ)) / (n : ℝ)))) := by
  let n := Q.natDegree
  let w := circleMap 0 ρ (θ / (n : ℝ))
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hdeg.ne'
  have hDegreeC : (Q.natDegree : ℂ) ≠ 0 := hnc
  have hw : w ∈ exteriorDisk := by
    change 1 < ‖w‖
    simpa [w, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hρ)] using hρ
  have hpow : w ^ n = circleMap 0 (ρ ^ n) θ := by
    simp only [w, circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_pow]
    congr 2
    field_simp [hnc]
  dsimp
  rw [← hpow, polynomial_exterior_fiber_roots Q hdeg F hF hidentity w hw]
  congr 1
  funext j
  congr 1
  simp only [w, circleMap, zero_add, ← Complex.exp_nat_mul,
    mul_assoc, ← Complex.exp_add, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  congr 2
  field_simp [hnc, hDegreeC]
  ring

end SpringerLean
