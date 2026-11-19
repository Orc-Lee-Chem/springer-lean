import SpringerLean.Round1452ChordNonnegative
import SpringerLean.Round1417RefinedTwoCircleCost

open scoped ComplexConjugate

namespace SpringerLean

/-- Two assigned refined caps can be replaced by their moving chords,
provided the relevant projection lies before its arc mean. This uses
one finite convex comparison for both sides, so each saving is counted
exactly once. -/
theorem exteriorInverseCoeff_le_of_two_refinedAffine_chord_caps
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n)
    (ξ₁ ξ₂ : ℂ) (hξ₁ : ‖ξ₁‖ = 1) (hξ₂ : ‖ξ₂‖ = 1)
    (W₁ W₂ x₁ x₂ μ₁ μ₂ : ℝ)
    (hW₁0 : 0 ≤ W₁) (hW₁ : W₁ ≤ 1/500)
    (hW₂0 : 0 ≤ W₂) (hW₂ : W₂ ≤ 1/500)
    (hμ₁ : x₁ < μ₁) (hμ₂ : x₂ < μ₂)
    (hcap : ∀ w ∈ exteriorOmitted F,
      (‖w‖ ≤ refinedAffineRadius W₁ (conj ξ₁*w).re ∧
        (conj ξ₁*w).re ≤ μ₁) ∨
      (‖w‖ ≤ refinedAffineRadius W₂ (conj ξ₂*w).re ∧
        (conj ξ₂*w).re ≤ μ₂)) :
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ => refinedAffineChordPower W₁ n x₁ μ₁ (2*ζ.re)) 0 1 +
      Real.circleAverage
        (fun ζ : ℂ => refinedAffineChordPower W₂ n x₂ μ₂ (2*ζ.re)) 0 1 := by
  let ξ : Fin 2 → ℂ := fun i => if i=0 then ξ₁ else ξ₂
  let W : Fin 2 → ℝ := fun i => if i=0 then W₁ else W₂
  let x : Fin 2 → ℝ := fun i => if i=0 then x₁ else x₂
  let μ : Fin 2 → ℝ := fun i => if i=0 then μ₁ else μ₂
  have hξ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ‖ξ i‖=1 := by
    intro i _
    fin_cases i <;> simp [ξ,hξ₁,hξ₂]
  have hcapSum : ∀ w ∈ exteriorOmitted F,
      ‖w‖^n ≤ ∑ i : Fin 2,
        refinedAffineChordPower (W i) n (x i) (μ i)
          (conj (ξ i)*w).re := by
    intro w hw
    have hside := hcap w hw
    have hzero₁ : 0 ≤ refinedAffineChordPower W₁ n x₁ μ₁
        (conj ξ₁*w).re :=
      refinedAffineChordPower_nonneg W₁ n hW₁0 hW₁ hμ₁
    have hzero₂ : 0 ≤ refinedAffineChordPower W₂ n x₂ μ₂
        (conj ξ₂*w).re :=
      refinedAffineChordPower_nonneg W₂ n hW₂0 hW₂ hμ₂
    rw [Fin.sum_univ_two]
    simp only [ξ,W,x,μ,↓reduceIte,Fin.zero_eta,Fin.isValue,
      zero_ne_one,ite_false]
    rcases hside with hleft | hright
    · have hchord := refinedAffinePower_le_chordPower W₁ n
        hμ₁ hleft.2
      have hpow := pow_le_pow_left₀ (norm_nonneg w) hleft.1 n
      exact (hpow.trans hchord).trans
        (le_add_of_nonneg_right hzero₂)
    · have hchord := refinedAffinePower_le_chordPower W₂ n
        hμ₂ hright.2
      have hpow := pow_le_pow_left₀ (norm_nonneg w) hright.1 n
      exact (hpow.trans hchord).trans
        (le_add_of_nonneg_left hzero₁)
  have h := exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps
    (S := Finset.univ) F hc n hn ξ hξ
    (fun i : Fin 2 => fun z : ℝ =>
      refinedAffineChordPower (W i) n (x i) (μ i) z)
    (by
      intro i hi
      fin_cases i
      · exact refinedAffineChordPower_convexOn W₁ n hμ₁
      · exact refinedAffineChordPower_convexOn W₂ n hμ₂)
    0 (by simpa using hcapSum)
  simpa [ξ,W,x,μ,Fin.sum_univ_two] using h

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_le_of_two_refinedAffine_chord_caps
