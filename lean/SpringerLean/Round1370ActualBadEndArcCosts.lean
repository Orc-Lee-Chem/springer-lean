import SpringerLean.Round1367ArcMeanScalar
import SpringerLean.Round1368ActualFirstChordCost
import SpringerLean.Round1369ActualSecondChordCost

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual first bad endpoint admits the canonical centered-arc
chord test. Its strict integrated saving is the remaining step. -/
theorem exteriorInverseCoeff_le_first_bad_arc_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1501 ≤ n) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) < ‖P₁‖)
    (hR₂ : (39/20 : ℝ) < ‖P₂‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hbad : ‖P₁‖ ≤ 2-1/(n:ℝ)) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseChordPower n
          (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1 +
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 := by
  dsimp
  obtain ⟨_,h₀μ,hμ,_⟩ := coarseArc_mean_bounds n hn
  exact exteriorInverseCoeff_le_selected_first_chord_cost F hc n
    (by omega) P₁ P₂ hP₁ hP₂ hR₁ hR₂ hP₁max hP₂neg hP₂max
    h₀μ (hbad.trans hμ)

/-- The identical canonical arc test applies to the selected second
endpoint when that endpoint has deficit at least `1/n`. -/
theorem exteriorInverseCoeff_le_second_bad_arc_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1501 ≤ n) (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) < ‖P₁‖)
    (hR₂ : (39/20 : ℝ) < ‖P₂‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hbad : ‖P₂‖ ≤ 2-1/(n:ℝ)) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1 +
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseChordPower n
          (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1 := by
  dsimp
  obtain ⟨_,h₀μ,hμ,_⟩ := coarseArc_mean_bounds n hn
  exact exteriorInverseCoeff_le_selected_second_chord_cost F hc n
    (by omega) P₁ P₂ hP₁ hP₂ hR₁ hR₂ hP₁max hP₂neg hP₂max
    h₀μ (hbad.trans hμ)

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_le_first_bad_arc_cost
#print axioms SpringerLean.exteriorInverseCoeff_le_second_bad_arc_cost
