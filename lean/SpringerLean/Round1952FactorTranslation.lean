import SpringerLean.Round1951FactorNormAlgebra

open Polynomial

namespace SpringerLean

/-- Translation of a plane set by a complex vector. -/
def continuumTranslate (K : Set ℂ) (b : ℂ) : Set ℂ :=
  (fun z => z + b) '' K

/-- A polynomial uniform norm on a translated set is a norm of the
correspondingly composed polynomial on the original set. -/
theorem continuumPolynomialNorm_translate
    (K : Set ℂ) (b : ℂ) (P : ℂ[X]) :
    continuumPolynomialNorm (continuumTranslate K b) P =
      continuumPolynomialNorm K (P.comp (X + C b)) := by
  unfold continuumPolynomialNorm continuumTranslate
  congr 1
  ext r
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z + b, ⟨z, hz, rfl⟩, ?_⟩
    simp

/-- Composition by a translation preserves the natural degree, even
for the zero polynomial. -/
theorem natDegree_comp_translation
    (P : ℂ[X]) (b : ℂ) :
    (P.comp (X + C b)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

/-- Admissibility of a factor constant passes to every translate. -/
theorem FactorInequality_translate
    (K : Set ℂ) (b : ℂ) (c : ℝ)
    (hc : FactorInequality K c) :
    FactorInequality (continuumTranslate K b) c := by
  intro r P
  have h := hc r (fun i : Fin r => (P i).comp (X + C b))
  simp_rw [continuumPolynomialNorm_translate K b]
  have hdegree :
      (∑ i : Fin r, ((P i).comp (X + C b)).natDegree) =
        ∑ i : Fin r, (P i).natDegree := by
    simp [natDegree_comp_translation]
  rw [hdegree] at h
  have hprod :
      (∏ i : Fin r, (P i).comp (X + C b)) =
        (∏ i : Fin r, P i).comp (X + C b) := by
    rw [prod_comp]
  rw [hprod] at h
  exact h

/-- Translating back by the opposite vector restores the original
plane set, with no compactness assumption. -/
theorem continuumTranslate_translate_neg
    (K : Set ℂ) (b : ℂ) :
    continuumTranslate (continuumTranslate K b) (-b) = K := by
  ext z
  change z ∈ (fun w : ℂ => w + -b) ''
      ((fun w : ℂ => w + b) '' K) ↔ z ∈ K
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, hzeq⟩
    have h : u = z := by simpa [add_assoc] using hzeq
    exact h ▸ hu
  · intro hz
    refine ⟨z + b, ⟨z, hz, rfl⟩, ?_⟩
    simp

theorem FactorInequality_translate_iff
    (K : Set ℂ) (b : ℂ) (c : ℝ) :
    FactorInequality (continuumTranslate K b) c ↔
      FactorInequality K c := by
  constructor
  · intro h
    have hback := FactorInequality_translate
      (continuumTranslate K b) (-b) c h
    simpa only [continuumTranslate_translate_neg] using hback
  · exact FactorInequality_translate K b c

/-- The least polynomial factor constant is invariant under every
translation of the actual plane set. -/
theorem factorConstant_translate
    (K : Set ℂ) (b : ℂ) :
    factorConstant (continuumTranslate K b) = factorConstant K := by
  have hset :
      {c : ℝ | 0 ≤ c ∧ FactorInequality (continuumTranslate K b) c} =
        {c : ℝ | 0 ≤ c ∧ FactorInequality K c} := by
    ext c
    simp only [Set.mem_setOf_eq, FactorInequality_translate_iff]
  simp only [factorConstant, hset]

end SpringerLean

#print axioms SpringerLean.continuumPolynomialNorm_translate
#print axioms SpringerLean.FactorInequality_translate
#print axioms SpringerLean.factorConstant_translate
