import SpringerLean.Round1453TwoChordCircleCost
import SpringerLean.Round1415CandidateTwoAffineCaps

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 250000

/-- Both selected actual endpoints pay their own moving-chord circle
cost in one convex comparison. The two arc savings can therefore be
subtracted simultaneously. -/
theorem exteriorInverseCoeff_candidate_selected_two_moving_chord_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧
      Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ P₁ P₂ : ℂ,
      P₁ ∈ exteriorOmitted F ∧ P₂ ∈ exteriorOmitted F ∧
      (359/180:ℝ) < ‖P₁‖ ∧ (39/20:ℝ) < ‖P₂‖ ∧
      0 < 2-‖P₁‖ ∧ 0 < 2-‖P₂‖ ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₁‖) < 1 ∧
      ((2*k-1:ℕ):ℝ)*(2-‖P₂‖) < 1 ∧
      (let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
          (1+Real.sqrt (2-‖P₁‖)/10))^2
       let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
          (1+Real.sqrt (2-‖P₂‖)/10))^2
       let b₁ : ℝ := Real.sqrt (3*(2-‖P₁‖))
       let b₂ : ℝ := Real.sqrt (3*(2-‖P₂‖))
       let μ₁ : ℝ := 2*Real.sin b₁/b₁
       let μ₂ : ℝ := 2*Real.sin b₂/b₂
       ((2*k-1:ℕ):ℝ)*‖exteriorInverseCoeff F (2*k-1)‖ ≤
         Real.circleAverage
           (fun ζ : ℂ => refinedAffineChordPower W₁ (2*k-1)
             (2*Real.cos b₁) μ₁ (2*ζ.re)) 0 1 +
         Real.circleAverage
           (fun ζ : ℂ => refinedAffineChordPower W₂ (2*k-1)
             (2*Real.cos b₂) μ₂ (2*ζ.re)) 0 1) ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖) ∧
      (conj (P₁/(‖P₁‖:ℂ))*P₂).re ≤ 0 ∧
      (∀ w ∈ convexHull ℝ (exteriorOmitted F),
        (conj (P₁/(‖P₁‖:ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hmax₁,hneg,hmax₂,
    hd₁,hd₂,hdef₁,hdef₂,hcaps⟩ :=
    exteriorOmitted_exists_candidate_two_assigned_affine_caps
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  let d₁ : ℝ := 2-‖P₁‖
  let d₂ : ℝ := 2-‖P₂‖
  let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
    (1+Real.sqrt d₁/10))^2
  let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
    (1+Real.sqrt d₂/10))^2
  let b₁ : ℝ := Real.sqrt (3*d₁)
  let b₂ : ℝ := Real.sqrt (3*d₂)
  let μ₁ : ℝ := 2*Real.sin b₁/b₁
  let μ₂ : ℝ := 2*Real.sin b₂/b₂
  let ξ₁ : ℂ := P₁/(‖P₁‖:ℝ)
  let ξ₂ : ℂ := P₂/(‖P₂‖:ℝ)
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hdef₁' : (n:ℝ)*d₁<1 := hdef₁
  have hdef₂' : (n:ℝ)*d₂<1 := hdef₂
  have hd₁' : d₁ ≤ 1/1501 := by
    have hh : (1501:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hd₁.le]
  have hd₂' : d₂ ≤ 1/1501 := by
    have hh : (1501:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hd₂.le]
  have hmean₁ := refinedArc_mean_bounds hd₁ hd₁'
  have hmean₂ := refinedArc_mean_bounds hd₂ hd₂'
  have hμ₁ : 2*Real.cos b₁ < μ₁ := hmean₁.2.2.1
  have hμ₂ : 2*Real.cos b₂ < μ₂ := hmean₂.2.2.1
  have hμR₁ : ‖P₁‖ ≤ μ₁ := by
    have hh := hmean₁.2.2.2.1
    change 2-d₁ ≤ μ₁ at hh
    dsimp [d₁] at hh
    linarith
  have hμR₂ : ‖P₂‖ ≤ μ₂ := by
    have hh := hmean₂.2.2.2.1
    change 2-d₂ ≤ μ₂ at hh
    dsimp [d₂] at hh
    linarith
  have hW₁ := mediumWidth_actual_window hn hd₁ hdef₁'
  have hW₂ := mediumWidth_actual_window hn hd₂ hdef₂'
  have hW₁' : 0 ≤ W₁ ∧ W₁ ≤ 1/500 := by
    constructor
    · dsimp [W₁,d₁]
      simpa only [show (2:ℝ)-(2-‖P₁‖)=‖P₁‖ by ring] using hW₁.1
    · dsimp [W₁,d₁]
      simpa only [show (2:ℝ)-(2-‖P₁‖)=‖P₁‖ by ring] using hW₁.2.1.le
  have hW₂' : 0 ≤ W₂ ∧ W₂ ≤ 1/500 := by
    constructor
    · dsimp [W₂,d₂]
      simpa only [show (2:ℝ)-(2-‖P₂‖)=‖P₂‖ by ring] using hW₂.1
    · dsimp [W₂,d₂]
      simpa only [show (2:ℝ)-(2-‖P₂‖)=‖P₂‖ by ring] using hW₂.2.1.le
  have hP₁ne : P₁ ≠ 0 := by
    intro hh
    simp [hh] at hR₁
    norm_num at hR₁
  have hP₂ne : P₂ ≠ 0 := by
    intro hh
    simp [hh] at hR₂
    norm_num at hR₂
  have hξ₁ : ‖ξ₁‖=1 := by dsimp [ξ₁]; simp [hP₁ne]
  have hξ₂ : ‖ξ₂‖=1 := by dsimp [ξ₂]; simp [hP₂ne]
  have hcover : ∀ w ∈ exteriorOmitted F,
      (‖w‖ ≤ refinedAffineRadius W₁ (conj ξ₁*w).re ∧
        (conj ξ₁*w).re ≤ μ₁) ∨
      (‖w‖ ≤ refinedAffineRadius W₂ (conj ξ₂*w).re ∧
        (conj ξ₂*w).re ≤ μ₂) := by
    intro w hw
    have hwHull : w ∈ convexHull ℝ (exteriorOmitted F) :=
      subset_convexHull ℝ _ hw
    by_cases hforward : 0 ≤ (conj ξ₁*w).re
    · left
      have hcap := hcaps.1 w hwHull hforward
      have hproj : (conj ξ₁*w).re ≤ ‖w‖ := by
        calc
          (conj ξ₁*w).re ≤ ‖conj ξ₁*w‖ := Complex.re_le_norm _
          _ = ‖w‖ := by simp [norm_mul,hξ₁]
      constructor
      · change ‖w‖ ≤ refinedAffineRadius W₁ (conj ξ₁*w).re at hcap
        exact hcap
      · exact (hproj.trans (hmax₁ w hwHull)).trans hμR₁
    · right
      have hfar : (conj ξ₁*w).re ≤ 0 :=
        le_of_lt (lt_of_not_ge hforward)
      have hcap := hcaps.2 w hwHull hfar
      have hproj : (conj ξ₂*w).re ≤ ‖w‖ := by
        calc
          (conj ξ₂*w).re ≤ ‖conj ξ₂*w‖ := Complex.re_le_norm _
          _ = ‖w‖ := by simp [norm_mul,hξ₂]
      constructor
      · change ‖w‖ ≤ refinedAffineRadius W₂ (conj ξ₂*w).re at hcap
        exact hcap
      · exact (hproj.trans (hmax₂ w hwHull hfar)).trans hμR₂
  have hcost := exteriorInverseCoeff_le_of_two_refinedAffine_chord_caps
    F hc n (by omega) ξ₁ ξ₂ hξ₁ hξ₂
    W₁ W₂ (2*Real.cos b₁) (2*Real.cos b₂) μ₁ μ₂
    hW₁'.1 hW₁'.2 hW₂'.1 hW₂'.2 hμ₁ hμ₂ hcover
  refine ⟨P₁,P₂,hP₁,hP₂,hR₁,hR₂,hd₁,hd₂,hdef₁,hdef₂,?_,hmax₁,hneg,hmax₂⟩
  simpa only [n,d₁,d₂,W₁,W₂,b₁,b₂,μ₁,ξ₁,ξ₂] using hcost

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_selected_two_moving_chord_cost
