import SpringerLean.Round1416RefinedAffineConvex
import SpringerLean.Round663ActualConvexCaps

open scoped ComplexConjugate

namespace SpringerLean

/-- An actual omitted-set cover by two refined affine projection tests
gives the sum of their normalized comparison-circle costs. -/
theorem exteriorInverseCoeff_le_of_two_refinedAffine_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n)
    (ξ₁ ξ₂ : ℂ) (hξ₁ : ‖ξ₁‖ = 1) (hξ₂ : ‖ξ₂‖ = 1)
    (W₁ W₂ : ℝ)
    (hcap : ∀ w ∈ exteriorOmitted F,
      ‖w‖ ≤ refinedAffineRadius W₁ (conj ξ₁*w).re ∨
      ‖w‖ ≤ refinedAffineRadius W₂ (conj ξ₂*w).re) :
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^n) 0 1 +
      Real.circleAverage
        (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^n) 0 1 := by
  let ξ : Fin 2 → ℂ := fun i => if i=0 then ξ₁ else ξ₂
  let W : Fin 2 → ℝ := fun i => if i=0 then W₁ else W₂
  have hξ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ‖ξ i‖ = 1 := by
    intro i _
    fin_cases i <;> simp [ξ,hξ₁,hξ₂]
  have hcapSum : ∀ w ∈ exteriorOmitted F,
      ‖w‖^n ≤ ∑ i : Fin 2,
        refinedAffineRadius (W i) (conj (ξ i)*w).re^n := by
    intro w hw
    have hside := hcap w hw
    have hzero₁ : 0 ≤ refinedAffineRadius W₁ (conj ξ₁*w).re^n :=
      pow_nonneg (refinedAffineRadius_pos _ _).le _
    have hzero₂ : 0 ≤ refinedAffineRadius W₂ (conj ξ₂*w).re^n :=
      pow_nonneg (refinedAffineRadius_pos _ _).le _
    rw [Fin.sum_univ_two]
    simp only [ξ,W,↓reduceIte,Fin.zero_eta,Fin.isValue,zero_ne_one,ite_false]
    rcases hside with hleft | hright
    · exact (pow_le_pow_left₀ (norm_nonneg w) hleft n).trans
        (le_add_of_nonneg_right hzero₂)
    · exact (pow_le_pow_left₀ (norm_nonneg w) hright n).trans
        (le_add_of_nonneg_left hzero₁)
  have h := exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps
    (S := Finset.univ) F hc n hn ξ hξ
    (fun i : Fin 2 => fun x : ℝ => refinedAffineRadius (W i) x^n)
    (by intro i hi; exact refinedAffineRadius_pow_convexOn (W i) n)
    0 (by simpa using hcapSum)
  simpa [ξ,W,Fin.sum_univ_two] using h

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_le_of_two_refinedAffine_caps
