import SpringerLean.Round1461Platform0018Moment

namespace SpringerLean

/-- A single normalized ledger converts the actual two-saving budget,
candidate moment reserve, platform reserve, and endpoint width bounds
into the joint J inequality. The saving shapes remain abstract here. -/
theorem refinedAffine_joint_budget_scalar
    {N I P B W₁ W₂ U₁ U₂ X₁ X₂ : ℝ}
    (hN : 0 < N) (hI : 0 < I)
    (hW₁0 : 0 ≤ W₁) (hW₂0 : 0 ≤ W₂)
    (hU₁ : W₁ ≤ U₁) (hU₂ : W₂ ≤ U₂)
    (hBudget : N*B+(67/1000:ℝ)*I*X₁+
        (67/1000:ℝ)*I*X₂ <
      2*P+(I/2)*(2+(57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*N*(W₁^2+W₂^2)))
    (hCandidate : (1-(251/500:ℝ)/N)*I ≤ N*B)
    (hPlatform : 2*N*P < (18/1000:ℝ)*I) :
    (67/1000:ℝ)*N*(X₁+X₂)-
      (285/1000:ℝ)*N*(U₁+U₂)-
      (275/1000:ℝ)*N^2*(U₁^2+U₂^2) < 52/100 := by
  have hU₁0 : 0 ≤ U₁ := hW₁0.trans hU₁
  have hU₂0 : 0 ≤ U₂ := hW₂0.trans hU₂
  have hsq₁ : W₁^2 ≤ U₁^2 :=
    pow_le_pow_left₀ hW₁0 hU₁ 2
  have hsq₂ : W₂^2 ≤ U₂^2 :=
    pow_le_pow_left₀ hW₂0 hU₂ 2
  have herror : (I/2)*((57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*N*(W₁^2+W₂^2)) ≤
      (I/2)*((57/100:ℝ)*(U₁+U₂)+
        (55/100:ℝ)*N*(U₁^2+U₂^2)) := by
    have hsum : (57/100:ℝ)*(W₁+W₂)+
          (55/100:ℝ)*N*(W₁^2+W₂^2) ≤
        (57/100:ℝ)*(U₁+U₂)+
          (55/100:ℝ)*N*(U₁^2+U₂^2) := by
      nlinarith [hU₁,hU₂,hsq₁,hsq₂,
        mul_nonneg hN.le (sub_nonneg.mpr hsq₁),
        mul_nonneg hN.le (sub_nonneg.mpr hsq₂)]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have h1 : (67/1000:ℝ)*I*(X₁+X₂) <
      2*P+(251/500:ℝ)/N*I+
        (I/2)*((57/100:ℝ)*(W₁+W₂)+
          (55/100:ℝ)*N*(W₁^2+W₂^2)) := by
    nlinarith [hBudget,hCandidate]
  have h2 : (67/1000:ℝ)*I*(X₁+X₂) <
      2*P+(251/500:ℝ)/N*I+
        (I/2)*((57/100:ℝ)*(U₁+U₂)+
          (55/100:ℝ)*N*(U₁^2+U₂^2)) := by
    linarith [h1,herror]
  have hmul := mul_lt_mul_of_pos_left h2 hN
  have hcancel : N*((251/500:ℝ)/N*I)=(251/500:ℝ)*I := by
    field_simp [ne_of_gt hN]
  have h3 : I*((67/1000:ℝ)*N*(X₁+X₂)-
        (285/1000:ℝ)*N*(U₁+U₂)-
        (275/1000:ℝ)*N^2*(U₁^2+U₂^2)) <
      2*N*P+(251/500:ℝ)*I := by
    nlinarith [hmul,hcancel]
  have h4 : I*((67/1000:ℝ)*N*(X₁+X₂)-
        (285/1000:ℝ)*N*(U₁+U₂)-
        (275/1000:ℝ)*N^2*(U₁^2+U₂^2)) <
      (52/100:ℝ)*I := by
    nlinarith [h3,hPlatform]
  let J : ℝ := (67/1000:ℝ)*N*(X₁+X₂)-
    (285/1000:ℝ)*N*(U₁+U₂)-
    (275/1000:ℝ)*N^2*(U₁^2+U₂^2)
  change J < 52/100
  have h4' : I*(J-52/100) < 0 := by
    dsimp [J]
    nlinarith [h4]
  by_contra hnot
  have hdiff : 0 ≤ J-52/100 := by linarith
  nlinarith [mul_nonneg hI.le hdiff]

end SpringerLean

#print axioms SpringerLean.refinedAffine_joint_budget_scalar
