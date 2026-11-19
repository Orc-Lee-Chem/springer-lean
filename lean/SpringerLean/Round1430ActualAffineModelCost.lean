import SpringerLean.Round1429AffineCostIntegral
import SpringerLean.Round1418CandidateTwoCircleCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Apply the one-end circle estimate to the squared width of an
actual odd-root strip, with no auxiliary width hypothesis. -/
theorem refinedAffine_actual_endpoint_circle_cost
    {n : ℕ} (hn : 1501 ≤ n) {d : ℝ}
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let W : ℝ := (exteriorRealRootWidth (2-d)
      (1+Real.sqrt d/10))^2
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1 ≤
      (19/10:ℝ)^n+
        (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2)*
          (1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2) := by
  dsimp
  obtain ⟨hW0,hW,hWsq⟩ := mediumWidth_actual_window hn hd0 hnd
  exact refinedAffineModelCircle_le n hW0 hW.le hWsq.le

/-- Adding two one-end costs retains the exact `I_n/2` normalization
and each endpoint's own strip width. -/
theorem refinedAffine_two_circle_model_cost
    (n : ℕ) {W₁ W₂ : ℝ}
    (hW₁ : 0 ≤ W₁ ∧ W₁ ≤ 1/500 ∧ (n:ℝ)*W₁^2 ≤ 3/500)
    (hW₂ : 0 ≤ W₂ ∧ W₂ ≤ 1/500 ∧ (n:ℝ)*W₂^2 ≤ 3/500) :
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^n) 0 1 +
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^n) 0 1 ≤
      2*(19/10:ℝ)^n+
        (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2)*
          (2+(57/100:ℝ)*(W₁+W₂)+
            (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2)) := by
  have h₁ := refinedAffineModelCircle_le n hW₁.1 hW₁.2.1 hW₁.2.2
  have h₂ := refinedAffineModelCircle_le n hW₂.1 hW₂.2.1 hW₂.2.2
  have hh := add_le_add h₁ h₂
  convert hh using 1 <;> ring

/-- For the same selected omitted endpoints produced by the Catalan
candidate argument, the actual inverse coefficient pays only the
explicit affine model budget. -/
theorem exteriorInverseCoeff_candidate_two_refined_model_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      (359/180:ℝ) < ‖P₁‖ ∧ (39/20:ℝ) < ‖P₂‖ ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 1 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 1 ∧
      (let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
          (1+Real.sqrt (2-‖P₁‖)/10))^2
       let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
          (1+Real.sqrt (2-‖P₂‖)/10))^2
       let I : ℝ := Real.circleAverage
          (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1
       ((2*k-1:ℕ):ℝ)*‖exteriorInverseCoeff F (2*k-1)‖ ≤
         2*(19/10:ℝ)^(2*k-1)+(I/2)*
           (2+(57/100:ℝ)*(W₁+W₂)+
             (55/100:ℝ)*((2*k-1:ℕ):ℝ)*(W₁^2+W₂^2))) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hmax,hneg,hmax₂,
      hd₁,hd₂,hdef₁,hdef₂,hcost⟩ :=
    exteriorInverseCoeff_candidate_two_refined_circle_cost
      F hc k hk hB hns
  let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
    (1+Real.sqrt (2-‖P₁‖)/10))^2
  let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
    (1+Real.sqrt (2-‖P₂‖)/10))^2
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1
  have hn : 1501 ≤ 2*k-1 := by omega
  have hV₁ : Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^(2*k-1)) 0 1 ≤
      (19/10:ℝ)^(2*k-1)+(I/2)*
        (1+(57/100:ℝ)*W₁+
          (55/100:ℝ)*((2*k-1:ℕ):ℝ)*W₁^2) := by
    have hh := refinedAffine_actual_endpoint_circle_cost hn hd₁ hdef₁
    have hsimp : 2-(2-‖P₁‖)=‖P₁‖ := by ring
    simpa only [hsimp] using hh
  have hV₂ : Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^(2*k-1)) 0 1 ≤
      (19/10:ℝ)^(2*k-1)+(I/2)*
        (1+(57/100:ℝ)*W₂+
          (55/100:ℝ)*((2*k-1:ℕ):ℝ)*W₂^2) := by
    have hh := refinedAffine_actual_endpoint_circle_cost hn hd₂ hdef₂
    have hsimp : 2-(2-‖P₂‖)=‖P₂‖ := by ring
    simpa only [hsimp] using hh
  change ((2*k-1:ℕ):ℝ)*‖exteriorInverseCoeff F (2*k-1)‖ ≤
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^(2*k-1)) 0 1 +
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^(2*k-1)) 0 1 at hcost
  have hsum := add_le_add hV₁ hV₂
  refine ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hmax,hneg,hmax₂,
    hd₁,hd₂,hdef₁,hdef₂,?_⟩
  change ((2*k-1:ℕ):ℝ)*‖exteriorInverseCoeff F (2*k-1)‖ ≤
    2*(19/10:ℝ)^(2*k-1)+(I/2)*
      (2+(57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*((2*k-1:ℕ):ℝ)*(W₁^2+W₂^2))
  have hbound := hcost.trans hsum
  convert hbound using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.refinedAffine_actual_endpoint_circle_cost
#print axioms SpringerLean.refinedAffine_two_circle_model_cost
#print axioms SpringerLean.exteriorInverseCoeff_candidate_two_refined_model_cost
