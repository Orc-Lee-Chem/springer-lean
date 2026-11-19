import SpringerLean.Round1462JointBudgetScalar

namespace SpringerLean
set_option maxHeartbeats 250000

/-- The dimensionless one-end localization expression. Its positive
term is the moving-chord saving; the two negative terms pay the
refined affine width costs. -/
noncomputable def refinedAffineJ (n : ℕ) (t : ℝ) : ℝ :=
  let z := (17/50:ℝ)*t*Real.log (2*(n:ℝ)/t)
  (67/1000:ℝ)*(n:ℝ)*t^2*Real.sqrt t*
    Real.exp (-(61/100:ℝ)*t)-
      (285/1000:ℝ)*z-(275/1000:ℝ)*z^2

theorem refinedAffine_z_deficit_eq
    {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : 0 < d) :
    (17/50:ℝ)*((n:ℝ)*d)*
      Real.log (2*(n:ℝ)/((n:ℝ)*d)) =
      (n:ℝ)*((17/50:ℝ)*d*Real.log (2/d)) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have harg : 2*(n:ℝ)/((n:ℝ)*d)=2/d := by
    field_simp [ne_of_gt hn0,ne_of_gt hd]
  rw [harg]
  ring

/-- The requested joint J bound for the same selected actual omitted
endpoints. The two savings enter through a single finite convex cap
comparison, and the circle normalization is common to all terms. -/
theorem exteriorInverseCoeff_candidate_actual_joint_J
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
      refinedAffineJ (2*k-1)
        (((2*k-1:ℕ):ℝ)*(2-‖P₁‖))+
      refinedAffineJ (2*k-1)
        (((2*k-1:ℕ):ℝ)*(2-‖P₂‖)) < 52/100 := by
  obtain ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hdef₁,hdef₂,hBudget⟩ :=
    exteriorInverseCoeff_candidate_two_moving_saving_budget
      F hc k hk hB hns
  let n : ℕ := 2*k-1
  let N : ℝ := n
  let d₁ : ℝ := 2-‖P₁‖
  let d₂ : ℝ := 2-‖P₂‖
  let t₁ : ℝ := N*d₁
  let t₂ : ℝ := N*d₂
  let W₁ : ℝ := (exteriorRealRootWidth ‖P₁‖
    (1+Real.sqrt d₁/10))^2
  let W₂ : ℝ := (exteriorRealRootWidth ‖P₂‖
    (1+Real.sqrt d₂/10))^2
  let U₁ : ℝ := (17/50)*d₁*Real.log (2/d₁)
  let U₂ : ℝ := (17/50)*d₂*Real.log (2/d₂)
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let B : ℝ := ‖exteriorInverseCoeff F n‖
  let P : ℝ := (19/10)^n
  let X₁ : ℝ := t₁^2*Real.sqrt t₁*
    Real.exp (-(61/100:ℝ)*t₁)
  let X₂ : ℝ := t₂^2*Real.sqrt t₂*
    Real.exp (-(61/100:ℝ)*t₂)
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0<n)
  have hIlo : (2:ℝ)^n/(2*N) ≤ I := by
    simpa only [n,N,I] using
      comparisonCircleMoment_odd_platform_lower k hk
  have hI : 0 < I := lt_of_lt_of_le (by positivity) hIlo
  have hCandidate0 := comparisonCircleMoment_candidate_0502_lower k hk
  have hNcat : N*(catalan (k-1):ℝ) ≤ N*B :=
    mul_le_mul_of_nonneg_left hB hN.le
  have hCandidate : (1-(251/500:ℝ)/N)*I ≤ N*B := by
    change (1-(251/500:ℝ)/N)*I ≤
      N*(catalan (k-1):ℝ) at hCandidate0
    exact hCandidate0.trans hNcat
  have hPlat0 := refinedAffine_platform_normalized_0018 k hk
  change 2*N*P/I < 18/1000 at hPlat0
  have hPlatform : 2*N*P < (18/1000:ℝ)*I :=
    (div_lt_iff₀ hI).mp hPlat0
  have hd₁cap : d₁ ≤ 1/1501 := by
    have hnR : (1501:ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hd₁.le,hdef₁]
  have hd₂cap : d₂ ≤ 1/1501 := by
    have hnR : (1501:ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) hd₂.le,hdef₂]
  have hW₁raw := mediumWidth_exact_width_sq_lt hd₁ hd₁cap
  have hW₂raw := mediumWidth_exact_width_sq_lt hd₂ hd₂cap
  have hW₁ : W₁ ≤ U₁ := by
    have hsimp : 2-d₁=‖P₁‖ := by dsimp [d₁]; ring
    rw [hsimp] at hW₁raw
    simpa [W₁,U₁,d₁,show (34/100:ℝ)=17/50 by norm_num] using
      hW₁raw.le
  have hW₂ : W₂ ≤ U₂ := by
    have hsimp : 2-d₂=‖P₂‖ := by dsimp [d₂]; ring
    rw [hsimp] at hW₂raw
    simpa [W₂,U₂,d₂,show (34/100:ℝ)=17/50 by norm_num] using
      hW₂raw.le
  have hW₁0 : 0 ≤ W₁ := sq_nonneg _
  have hW₂0 : 0 ≤ W₂ := sq_nonneg _
  have hBudget' : N*B+(67/1000:ℝ)*I*X₁+
      (67/1000:ℝ)*I*X₂ <
    2*P+(I/2)*(2+(57/100:ℝ)*(W₁+W₂)+
      (55/100:ℝ)*N*(W₁^2+W₂^2)) := by
    convert hBudget using 1 <;>
      (dsimp [N,B,I,P,X₁,X₂,t₁,t₂,W₁,W₂,d₁,d₂]; ring)
  have hJoint := refinedAffine_joint_budget_scalar
    hN hI hW₁0 hW₂0 hW₁ hW₂ hBudget' hCandidate hPlatform
  refine ⟨P₁,P₂,hP₁,hP₂,hd₁,hd₂,hdef₁,hdef₂,?_⟩
  have hz₁ := refinedAffine_z_deficit_eq
    (n := n) (by omega : 1≤n) hd₁
  have hz₂ := refinedAffine_z_deficit_eq
    (n := n) (by omega : 1≤n) hd₂
  change (17/50:ℝ)*t₁*Real.log (2*N/t₁)=N*U₁ at hz₁
  change (17/50:ℝ)*t₂*Real.log (2*N/t₂)=N*U₂ at hz₂
  dsimp [refinedAffineJ]
  rw [hz₁,hz₂]
  dsimp [t₁,t₂,N,d₁,d₂] at hJoint ⊢
  nlinarith [hJoint]

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_actual_joint_J
