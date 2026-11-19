import SpringerLean.Round1366ExactChordProfile
import SpringerLean.Round1360ActualTwoInverseCaps
import SpringerLean.Round663ActualConvexCaps

open scoped ComplexConjugate

namespace SpringerLean

/-- If the globally selected first endpoint is below the arc mean,
its exact profile may be replaced by the convex chord in the actual
inverse-coefficient estimate. Only the circle integral remains. -/
theorem exteriorInverseCoeff_le_selected_first_chord_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) < ‖P₁‖)
    (hR₂ : (39/20 : ℝ) < ‖P₂‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    {x₀ μ : ℝ} (h₀μ : x₀ < μ) (hbad : ‖P₁‖ ≤ μ) :
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseChordPower n x₀ μ (2*ζ.re)) 0 1 +
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 := by
  let ξ : Fin 2 → ℂ := fun i => if i = 0 then P₁/(‖P₁‖ : ℂ) else P₂/(‖P₂‖ : ℂ)
  let ψ : Fin 2 → ℝ → ℝ := fun i => if i = 0 then
    coarseInverseChordPower n x₀ μ else fun x => coarseInverseRadius x ^ n
  have hP₁ne : P₁ ≠ 0 := by
    intro hp
    simp [hp] at hR₁
    norm_num at hR₁
  have hP₂ne : P₂ ≠ 0 := by
    intro hp
    simp [hp] at hR₂
    norm_num at hR₂
  have hξ : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ‖ξ i‖ = 1 := by
    intro i _
    fin_cases i <;> simp [ξ, hP₁ne, hP₂ne]
  have hψ : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      ConvexOn ℝ Set.univ (ψ i) := by
    intro i _
    fin_cases i
    · exact coarseInverseChordPower_convexOn n h₀μ
    · exact coarseInverseRadius_pow_convexOn n
  have hcap : ∀ w ∈ exteriorOmitted F,
      ‖w‖^n ≤ ∑ i : Fin 2, ψ i ((conj (ξ i)*w).re) := by
    intro w hw
    have hwHull : w ∈ convexHull ℝ (exteriorOmitted F) :=
      subset_convexHull ℝ _ hw
    have hside := exteriorOmitted_selected_two_inverse_radius_cap
      F hc P₁ P₂ w hP₁ hP₂ hwHull hR₁ hR₂ hP₁max hP₂neg hP₂max
    have hx₁ : (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ ‖w‖ := by
      calc
        _ ≤ ‖conj (P₁/(‖P₁‖ : ℂ))*w‖ := Complex.re_le_norm _
        _ = ‖w‖ := by simp [norm_mul, hP₁ne]
    have hbase₂ : 0 ≤ coarseInverseRadius
        ((conj (P₂/(‖P₂‖ : ℂ))*w).re)^n :=
      pow_nonneg (coarseInverseRadius_pos _).le _
    have hchord₁ : 0 ≤ coarseInverseChordPower n x₀ μ
        ((conj (P₁/(‖P₁‖ : ℂ))*w).re) := by
      by_cases hx : (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ x₀
      · simp only [coarseInverseChordPower, if_pos hx]
        exact pow_nonneg (coarseInverseRadius_pos _).le _
      · -- The extended secant may be negative far to the left only;
        -- above `x₀` its slope is nonnegative and starts positive.
        have hfpos : 0 ≤ coarseInverseRadius x₀ ^ n :=
          pow_nonneg (coarseInverseRadius_pos _).le _
        have hmono : coarseInverseRadius x₀ ^ n ≤ coarseInverseRadius μ ^ n := by
          have hbase : coarseInverseRadius x₀ ≤ coarseInverseRadius μ :=
            coarseInverseRadius_mono h₀μ.le
          exact pow_le_pow_left₀ (coarseInverseRadius_pos _).le hbase n
        simp only [coarseInverseChordPower, if_neg hx]
        have hratio : 0 ≤ ((conj (P₁/(‖P₁‖ : ℂ))*w).re-x₀)/(μ-x₀) :=
          div_nonneg (by linarith [lt_of_not_ge hx]) (by linarith [h₀μ])
        nlinarith [mul_nonneg hratio (sub_nonneg.mpr hmono)]
    rw [Fin.sum_univ_two]
    simp only [ψ,ξ, ↓reduceIte, Fin.isValue]
    rcases hside with ⟨hfirst,hwR⟩ | ⟨hsecond,_⟩
    · have hxμ := (hx₁.trans hwR).trans hbad
      have hpow := pow_le_pow_left₀ (norm_nonneg w) hfirst n
      have hchord := coarseInversePower_le_chordPower n h₀μ hxμ
      exact (hpow.trans hchord).trans (le_add_of_nonneg_right hbase₂)
    · exact (pow_le_pow_left₀ (norm_nonneg w) hsecond n).trans
        (le_add_of_nonneg_left hchord₁)
  have h := exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps
    (S := Finset.univ) F hc n hn ξ hξ ψ hψ 0
    (by simpa using hcap)
  simpa [ψ, Fin.sum_univ_two] using h

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_le_selected_first_chord_cost
