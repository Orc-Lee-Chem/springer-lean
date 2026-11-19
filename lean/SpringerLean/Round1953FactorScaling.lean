import SpringerLean.Round1952FactorTranslation

open Polynomial

namespace SpringerLean

/-- Complex dilation of a plane set. -/
def continuumScale (K : Set ℂ) (a : ℂ) : Set ℂ :=
  (fun z => a * z) '' K

theorem continuumPolynomialNorm_scale
    (K : Set ℂ) (a : ℂ) (P : ℂ[X]) :
    continuumPolynomialNorm (continuumScale K a) P =
      continuumPolynomialNorm K (P.comp (C a * X)) := by
  unfold continuumPolynomialNorm continuumScale
  congr 1
  ext r
  constructor
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp
  · rintro ⟨z, hz, rfl⟩
    refine ⟨a * z, ⟨z, hz, rfl⟩, ?_⟩
    simp

theorem natDegree_comp_scale
    (P : ℂ[X]) (a : ℂ) (ha : a ≠ 0) :
    (P.comp (C a * X)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X a ha, mul_one]

theorem FactorInequality_scale
    (K : Set ℂ) (a : ℂ) (ha : a ≠ 0) (c : ℝ)
    (hc : FactorInequality K c) :
    FactorInequality (continuumScale K a) c := by
  intro r P
  have h := hc r (fun i : Fin r => (P i).comp (C a * X))
  simp_rw [continuumPolynomialNorm_scale K a]
  have hdegree :
      (∑ i : Fin r, ((P i).comp (C a * X)).natDegree) =
        ∑ i : Fin r, (P i).natDegree := by
    simp [natDegree_comp_scale, ha]
  rw [hdegree] at h
  have hprod :
      (∏ i : Fin r, (P i).comp (C a * X)) =
        (∏ i : Fin r, P i).comp (C a * X) := by
    rw [prod_comp]
  rw [hprod] at h
  exact h

theorem continuumScale_scale_inv
    (K : Set ℂ) (a : ℂ) (ha : a ≠ 0) :
    continuumScale (continuumScale K a) a⁻¹ = K := by
  ext z
  change z ∈ (fun w : ℂ => a⁻¹ * w) ''
      ((fun w : ℂ => a * w) '' K) ↔ z ∈ K
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, hzeq⟩
    have h : u = z := by simpa [mul_assoc, ha] using hzeq
    exact h ▸ hu
  · intro hz
    refine ⟨a * z, ⟨z, hz, rfl⟩, ?_⟩
    simp [mul_assoc, ha]

theorem FactorInequality_scale_iff
    (K : Set ℂ) (a : ℂ) (ha : a ≠ 0) (c : ℝ) :
    FactorInequality (continuumScale K a) c ↔
      FactorInequality K c := by
  constructor
  · intro h
    have hback := FactorInequality_scale
      (continuumScale K a) a⁻¹ (inv_ne_zero ha) c h
    simpa only [continuumScale_scale_inv K a ha] using hback
  · exact FactorInequality_scale K a ha c

/-- The actual least factor constant is unchanged by nonzero complex
dilation. Together with translation, this is similarity invariance. -/
theorem factorConstant_scale
    (K : Set ℂ) (a : ℂ) (ha : a ≠ 0) :
    factorConstant (continuumScale K a) = factorConstant K := by
  have hset :
      {c : ℝ | 0 ≤ c ∧ FactorInequality (continuumScale K a) c} =
        {c : ℝ | 0 ≤ c ∧ FactorInequality K c} := by
    ext c
    simp only [Set.mem_setOf_eq, FactorInequality_scale_iff K a ha c]
  simp only [factorConstant, hset]

/-- Every nondegenerate complex affine similarity preserves the least
factor constant of the actual plane set. -/
theorem factorConstant_similarity
    (K : Set ℂ) (a b : ℂ) (ha : a ≠ 0) :
    factorConstant (continuumTranslate (continuumScale K a) b) =
      factorConstant K := by
  rw [factorConstant_translate, factorConstant_scale K a ha]

end SpringerLean

#print axioms SpringerLean.continuumPolynomialNorm_scale
#print axioms SpringerLean.factorConstant_scale
#print axioms SpringerLean.factorConstant_similarity
