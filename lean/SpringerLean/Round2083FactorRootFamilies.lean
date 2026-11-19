import SpringerLean.Round1951FactorNormAlgebra
import SpringerLean.Round1947FactorLinearFamilies
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Polynomial Set
open scoped BigOperators

namespace SpringerLean

/-- The product of the norms of the linear factors bounds the norm
of their product, counting every root with its multiplicity. -/
private theorem continuumPolynomialNorm_multiset_linear_le
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (A : Multiset ℂ) :
    continuumPolynomialNorm K (A.map (fun a => X - C a)).prod ≤
      (A.map (continuumFarthestDistance K)).prod := by
  induction A using Multiset.induction_on with
  | empty =>
    obtain ⟨z,hz,hmax⟩ := continuumPolynomialNorm_attained K hK hne (1 : ℂ[X])
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [continuumPolynomialNorm_eq_at_max K hK hne (1 : ℂ[X]) hz hmax]
    simp
  | cons a A ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (continuumPolynomialNorm_mul_le K hK hne _ _).trans (by
      rw [← continuumFarthestDistance_eq_linear_norm]
      exact mul_le_mul_of_nonneg_left ih (by
        rw [continuumFarthestDistance_eq_linear_norm]
        exact continuumPolynomialNorm_nonneg K hK hne _))

/-- It suffices to control arbitrary finite families of linear
polynomials. Complex factorization then gives the original
inequality for all finite polynomial families. -/
theorem FactorInequality_of_linear_families
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ)
    (hlinear : ∀ (n : ℕ) (a : Fin n → ℂ),
      (∏ i : Fin n, continuumFarthestDistance K (a i)) ≤
        c^n * continuumPolynomialNorm K (∏ i : Fin n, (X - C (a i)))) :
    FactorInequality K c := by
  classical
  have hmulti (A : Multiset ℂ) :
      (A.map (continuumFarthestDistance K)).prod ≤
        c^A.card * continuumPolynomialNorm K (A.map (fun a => X-C a)).prod := by
    induction A using Quotient.inductionOn with
    | _ l =>
      have hl := hlinear l.length (fun i => l[i.1])
      change (l.map (continuumFarthestDistance K)).prod ≤
        c^l.length * continuumPolynomialNorm K (l.map (fun a => X-C a)).prod
      rw [← Fin.prod_univ_fun_getElem l (continuumFarthestDistance K),
        ← Fin.prod_univ_fun_getElem l (fun a => (X-C a : ℂ[X]))]
      exact hl
  intro m P
  by_cases hz : ∃ i, P i = 0
  · obtain ⟨i,hi⟩ := hz
    have hprod : (∏ j : Fin m, P j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hn0 : continuumPolynomialNorm K 0 = 0 := by
      obtain ⟨z,hz,hmax⟩ := continuumPolynomialNorm_attained K hK hne (0 : ℂ[X])
      rw [continuumPolynomialNorm_eq_at_max K hK hne (0 : ℂ[X]) hz hmax]
      simp
    have hprod0 : (∏ j : Fin m, continuumPolynomialNorm K (P j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,hn0])
    rw [hprod,hprod0,hn0,mul_zero]
  · let A (i : Fin m) := (P i).roots
    let a (i : Fin m) := (P i).leadingCoeff
    let L (B : Multiset ℂ) := (B.map (fun z => X - C z)).prod
    let D (B : Multiset ℂ) := (B.map (continuumFarthestDistance K)).prod
    let all := ∑ i : Fin m, A i
    have hdeg (i : Fin m) : (A i).card = (P i).natDegree :=
      (IsAlgClosed.splits (P i)).natDegree_eq_card_roots.symm
    have hfac (i : Fin m) : C (a i) * L (A i) = P i :=
      C_leadingCoeff_mul_prod_multiset_X_sub_C (hdeg i)
    have hgroup {R : Type} [CommMonoid R] (g : ℂ → R) (S : Finset (Fin m)) :
        ((∑ i ∈ S, A i).map g).prod = ∏ i ∈ S, ((A i).map g).prod := by
      induction S using Finset.induction_on with
      | empty => simp
      | insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add, Multiset.prod_add, ih]
    have hL : L all = ∏ i : Fin m, L (A i) := hgroup (fun z => (X-C z : ℂ[X])) Finset.univ
    have hD : D all = ∏ i : Fin m, D (A i) := hgroup (continuumFarthestDistance K) Finset.univ
    have hcard : all.card = ∑ i : Fin m, (P i).natDegree := by
      simp [all,hdeg]
    have hbound (i : Fin m) : continuumPolynomialNorm K (P i) ≤ ‖a i‖ * D (A i) := by
      rw [← hfac i, continuumPolynomialNorm_C_mul K hK hne]
      exact mul_le_mul_of_nonneg_left
        (continuumPolynomialNorm_multiset_linear_le K hK hne (A i)) (norm_nonneg _)
    have hpolys : (∏ i : Fin m, P i) = C (∏ i : Fin m, a i) * L all := by
      rw [hL, map_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => (hfac i).symm)
    have hall : D all ≤ c^all.card * continuumPolynomialNorm K (L all) := hmulti all
    calc
      _ ≤ ∏ i : Fin m, ‖a i‖ * D (A i) :=
        Finset.prod_le_prod₀
          (fun i _ => continuumPolynomialNorm_nonneg K hK hne (P i))
          (fun i _ => hbound i)
      _ = ‖∏ i : Fin m, a i‖ * D all := by
        rw [Finset.prod_mul_distrib, norm_prod, hD]
      _ ≤ ‖∏ i : Fin m, a i‖ * (c^all.card * continuumPolynomialNorm K (L all)) :=
        mul_le_mul_of_nonneg_left hall (norm_nonneg _)
      _ = _ := by
        rw [hpolys, continuumPolynomialNorm_C_mul K hK hne, hcard]
        ring

end SpringerLean
