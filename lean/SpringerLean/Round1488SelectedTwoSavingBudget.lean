import SpringerLean.Round1487SelectedTwoChordCost
import SpringerLean.Round1455TwoChordBudget

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 200000

/-- The first actual two-end saving statement: the Catalan candidate's
inverse moment plus BOTH strictly positive moving-arc savings fits
inside the refined affine model budget. -/
theorem exteriorInverseCoeff_candidate_selected_two_moving_saving_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 1 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 1 ∧
      (let n : ℕ := 2*k-1
       let d₁ : ℝ := 2-‖P₁‖
       let d₂ : ℝ := 2-‖P₂‖
       let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
         (1+Real.sqrt d₁/10))^2
       let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
         (1+Real.sqrt d₂/10))^2
       let I : ℝ := Real.circleAverage
         (fun ζ : ℂ => |2*ζ.re|^n) 0 1
       let S₁ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₁)^2*
         Real.sqrt ((n:ℝ)*d₁)*
         Real.exp (-(61/100:ℝ)*((n:ℝ)*d₁))
       let S₂ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₂)^2*
         Real.sqrt ((n:ℝ)*d₂)*
         Real.exp (-(61/100:ℝ)*((n:ℝ)*d₂))
       (n:ℝ)*‖exteriorInverseCoeff F n‖+S₁+S₂ <
         2*(19/10:ℝ)^n+(I/2)*
           (2+(57/100:ℝ)*(W₁+W₂)+
             (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2))) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hd₁,hd₂,hdef₁,hdef₂,hcost,
    hmax₁,hneg,hmax₂⟩ :=
    exteriorInverseCoeff_candidate_selected_two_moving_chord_cost
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  let d₁ : ℝ := 2-‖P₁‖
  let d₂ : ℝ := 2-‖P₂‖
  let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
    (1+Real.sqrt d₁/10))^2
  let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
    (1+Real.sqrt d₂/10))^2
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let b₁ : ℝ := Real.sqrt (3*d₁)
  let b₂ : ℝ := Real.sqrt (3*d₂)
  let T₁ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W₁ n
      (2*Real.cos b₁) (2*Real.sin b₁/b₁) (2*ζ.re)) 0 1
  let T₂ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W₂ n
      (2*Real.cos b₂) (2*Real.sin b₂/b₂) (2*ζ.re)) 0 1
  let S₁ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₁)^2*
    Real.sqrt ((n:ℝ)*d₁)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₁))
  let S₂ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₂)^2*
    Real.sqrt ((n:ℝ)*d₂)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₂))
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hW₁ := mediumWidth_actual_window hn hd₁ hdef₁
  have hW₂ := mediumWidth_actual_window hn hd₂ hdef₂
  have hW₁' : 0 ≤ W₁ ∧ W₁ ≤ 1/500 ∧
      (n:ℝ)*W₁^2 ≤ 3/500 := by
    have hsimp : 2-d₁=‖P₁‖ := by dsimp [d₁]; ring
    change 0 ≤ (exteriorRealRootWidth (2-d₁)
        (1+Real.sqrt d₁/10))^2 ∧
      (exteriorRealRootWidth (2-d₁)
        (1+Real.sqrt d₁/10))^2 < 1/500 ∧
      (n:ℝ)*((exteriorRealRootWidth (2-d₁)
        (1+Real.sqrt d₁/10))^2)^2 < 3/500 at hW₁
    rw [hsimp] at hW₁
    exact ⟨hW₁.1,hW₁.2.1.le,hW₁.2.2.le⟩
  have hW₂' : 0 ≤ W₂ ∧ W₂ ≤ 1/500 ∧
      (n:ℝ)*W₂^2 ≤ 3/500 := by
    have hsimp : 2-d₂=‖P₂‖ := by dsimp [d₂]; ring
    change 0 ≤ (exteriorRealRootWidth (2-d₂)
        (1+Real.sqrt d₂/10))^2 ∧
      (exteriorRealRootWidth (2-d₂)
        (1+Real.sqrt d₂/10))^2 < 1/500 ∧
      (n:ℝ)*((exteriorRealRootWidth (2-d₂)
        (1+Real.sqrt d₂/10))^2)^2 < 3/500 at hW₂
    rw [hsimp] at hW₂
    exact ⟨hW₂.1,hW₂.2.1.le,hW₂.2.2.le⟩
  have hbudget := refinedAffine_two_moving_chords_budget
    n hn hW₁'.1 hW₁'.2.1 hW₁'.2.2
    hW₂'.1 hW₂'.2.1 hW₂'.2.2 hd₁ hdef₁ hd₂ hdef₂
  change T₁+T₂+S₁+S₂ <
    2*(19/10:ℝ)^n+(I/2)*
      (2+(57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2)) at hbudget
  change (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤ T₁+T₂ at hcost
  refine ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hdef₁,hdef₂,?_,hmax₁,hneg,hmax₂⟩
  change (n:ℝ)*‖exteriorInverseCoeff F n‖+S₁+S₂ <
    2*(19/10:ℝ)^n+(I/2)*
      (2+(57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2))
  linarith

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_moving_saving_budget
