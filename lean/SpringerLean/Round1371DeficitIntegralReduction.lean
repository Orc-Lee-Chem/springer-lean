import SpringerLean.Round1370ActualBadEndArcCosts
import SpringerLean.Round1354ActualCandidateMoment
import SpringerLean.Round1341CostContradictionScalar

open scoped ComplexConjugate

namespace SpringerLean

/-- Exact reduction of both selected `n dᵢ < 1` claims to two explicit
one-variable circle inequalities. Geometry, convex testing, the actual
inverse coefficient and Catalan normalization have been discharged.
The two circle inequalities are genuine hypotheses here, not claimed
as completed Lean proofs. -/
theorem candidate_selected_deficits_lt_one_of_exact_circle_bounds
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hR₁ : (39/20 : ℝ) < ‖P₁‖)
    (hR₂ : (39/20 : ℝ) < ‖P₂‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂neg : (conj (P₁/(‖P₁‖ : ℂ))*P₂).re ≤ 0)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖)
    (hmodel :
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^(2*k-1)) 0 1 ≤
      (39/20 : ℝ)^(2*k-1) +
        (Real.circleAverage
          (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 / 2) *
          (1+13/(((2*k-1:ℕ):ℝ))))
    (hsaving :
      let b : ℝ := Real.sqrt (3/(((2*k-1:ℕ):ℝ)))
      let I : ℝ := Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseChordPower (2*k-1)
          (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1 + I/100 <
      Real.circleAverage
        (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^(2*k-1)) 0 1) :
    (2-1/(((2*k-1:ℕ):ℝ)) < ‖P₁‖) ∧
    (2-1/(((2*k-1:ℕ):ℝ)) < ‖P₂‖) := by
  let n : ℕ := 2*k-1
  let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let V : ℝ := Real.circleAverage
    (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let T : ℝ := Real.circleAverage
    (fun ζ : ℂ => coarseInverseChordPower n
      (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hplat : 2*(39/20 : ℝ)^n ≤ I/(n:ℝ) := by
    simpa [n,I] using comparisonCircle_platform_bound k hk
  have hIpos : 0 < I := by
    have hp := (le_div_iff₀ hn0).1 hplat
    have hpositive : 0 < 2*(39/20 : ℝ)^n*(n:ℝ) := by positivity
    linarith
  have hmod : V ≤ (39/20 : ℝ)^n+(I/2)*(1+13/(n:ℝ)) := by
    simpa [n,I,V] using hmodel
  have hsave : T+I/100 < V := by
    simpa [n,I,V,T,b] using hsaving
  have htwo : T+V+I/100 < 2*(39/20 : ℝ)^n+I*(1+13/(n:ℝ)) := by
    have hsum := add_lt_add_of_lt_of_le hsave hmod
    nlinarith
  have hcost := two_side_model_cost_lt_candidate n hn hIpos hplat htwo
  have hcat : (1-1/(n:ℝ))*I ≤
      (n:ℝ)*(catalan (k-1) : ℝ) := by
    simpa [n,I] using comparisonCircleMoment_candidate_scalar_lower k (by omega)
  have hscaled : (n:ℝ)*(catalan (k-1) : ℝ) ≤
      (n:ℝ)*‖exteriorInverseCoeff F n‖ := by
    exact mul_le_mul_of_nonneg_left (by simpa [n] using hB) hn0.le
  constructor
  · by_contra hnot
    have hbad : ‖P₁‖ ≤ 2-1/(n:ℝ) := le_of_not_gt hnot
    have hactual := exteriorInverseCoeff_le_first_bad_arc_cost
      F hc n hn P₁ P₂ hP₁ hP₂ hR₁ hR₂ hP₁max hP₂neg hP₂max hbad
    change (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤ T+V at hactual
    have : (n:ℝ)*(catalan (k-1) : ℝ) <
        (n:ℝ)*(catalan (k-1) : ℝ) := by
      calc
        _ ≤ (n:ℝ)*‖exteriorInverseCoeff F n‖ := hscaled
        _ ≤ T+V := hactual
        _ < (1-1/(n:ℝ))*I := hcost
        _ ≤ (n:ℝ)*(catalan (k-1) : ℝ) := hcat
    exact (lt_irrefl _ this)
  · by_contra hnot
    have hbad : ‖P₂‖ ≤ 2-1/(n:ℝ) := le_of_not_gt hnot
    have hactual := exteriorInverseCoeff_le_second_bad_arc_cost
      F hc n hn P₁ P₂ hP₁ hP₂ hR₁ hR₂ hP₁max hP₂neg hP₂max hbad
    change (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤ V+T at hactual
    have : (n:ℝ)*(catalan (k-1) : ℝ) <
        (n:ℝ)*(catalan (k-1) : ℝ) := by
      calc
        _ ≤ (n:ℝ)*‖exteriorInverseCoeff F n‖ := hscaled
        _ ≤ V+T := hactual
        _ = T+V := add_comm _ _
        _ < (1-1/(n:ℝ))*I := hcost
        _ ≤ (n:ℝ)*(catalan (k-1) : ℝ) := hcat
    exact (lt_irrefl _ this)

end SpringerLean

#print axioms SpringerLean.candidate_selected_deficits_lt_one_of_exact_circle_bounds
