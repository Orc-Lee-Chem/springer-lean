import SpringerLean.Round1345AffineCircleCost
import SpringerLean.Round1346GaussianCatalanScalar

open scoped ComplexConjugate

namespace SpringerLean

/-- The coarse one-end model has strictly less mass than a Catalan
candidate at every `k ≥ 751`. Its circle average uses normalized
angular measure. -/
theorem affinePlatform_circleAverage_lt_Catalan
    (k : ℕ) (hk : 751 ≤ k) :
    Real.circleAverage
      (fun ζ : ℂ =>
        (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^(2*k-1)) 0 1 <
      (((2*k-1:ℕ):ℝ))*(catalan (k-1) : ℝ) := by
  let n : ℕ := 2*k-1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hG := affinePlatform_circleAverage_le_gaussian n hn
  have hs := gaussian_platform_lt_normalizedCatalan k hk
  have hpow : (39/20 : ℝ)^n = (2:ℝ)^n*(39/40 : ℝ)^n := by
    rw [show (39/20 : ℝ) = 2*(39/40 : ℝ) by norm_num, mul_pow]
  have hpow2 : (2:ℝ)^n = 2*(4:ℝ)^(k-1) := by
    have hid : n = 2*(k-1)+1 := by dsimp [n]; omega
    rw [hid, pow_add, pow_one,
      show (4:ℝ) = 2^2 by norm_num, pow_mul]
    ring
  have hcat : (2:ℝ)^n*normalizedCatalanOddMoment (k-1) =
      (n:ℝ)*(catalan (k-1) : ℝ) := by
    rw [hpow2]
    unfold normalizedCatalanOddMoment
    have hden : (0:ℝ) < 2*(4:ℝ)^(k-1) := by positivity
    have hid : 2*(k-1)+1 = n := by dsimp [n]; omega
    have hcast : 2*((k-1:ℕ):ℝ)+1 = (n:ℝ) := by
      exact_mod_cast hid
    calc
      (2*(4:ℝ)^(k-1)) *
          (scaledCatalanMoment (k-1)/(2*(4:ℝ)^(k-1))) =
          scaledCatalanMoment (k-1) := by field_simp
      _ = (n:ℝ)*(catalan (k-1) : ℝ) := by
        rw [scaledCatalanMoment, hcast]
  have hpos : 0 < (2:ℝ)^n := by positivity
  change Real.circleAverage
      (fun ζ : ℂ =>
        (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^n) 0 1 <
      (n:ℝ)*(catalan (k-1) : ℝ)
  calc
    _ ≤ (39/20 : ℝ)^n + (2:ℝ)^n *
      Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) /
        (2*Real.pi) := hG
    _ = (2:ℝ)^n * ((39/40 : ℝ)^n +
      Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) /
        (2*Real.pi)) := by rw [hpow]; ring
    _ < (2:ℝ)^n*normalizedCatalanOddMoment (k-1) :=
      mul_lt_mul_of_pos_left (by simpa [n] using hs) hpos
    _ = (n:ℝ)*(catalan (k-1) : ℝ) := hcat

/-- The selected opposite-half radius is strictly greater than
`39/20` for every actual Catalan candidate. The chosen maximizer is
the same one used in the half-plane selector; no new endpoint is
silently substituted. -/
theorem exteriorOmitted_candidate_second_radius_gt_39_20
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    (P₁ P₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₁big : (359/180 : ℝ) < ‖P₁‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj (P₁/(‖P₁‖ : ℂ))*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    (39/20 : ℝ) < ‖P₂‖ := by
  by_contra hsmall
  have hP₂small : ‖P₂‖ ≤ (39/20 : ℝ) := le_of_not_gt hsmall
  have hP₁big' : (39/20 : ℝ) ≤ ‖P₁‖ := by linarith
  have hP₁pos : 0 < ‖P₁‖ := by linarith
  have hP₁ne : P₁ ≠ 0 := by
    intro hp
    simp [hp] at hP₁big
    norm_num at hP₁big
  have hP₁0 : (‖P₁‖ : ℂ) ≠ 0 := by exact_mod_cast hP₁pos.ne'
  let ξ : ℂ := P₁/(‖P₁‖ : ℂ)
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ]
    simp [hP₁ne]
  have hP₁norm : P₁ = ξ*(‖P₁‖ : ℂ) := by
    dsimp [ξ]
    field_simp
  let n : ℕ := 2*k-1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hactual := exteriorInverseCoeff_le_affinePlatform_cost
    F hc n hn P₁ P₂ ξ hP₁ hξ hP₁norm hP₁big'
    hP₁max hP₂small hP₂max
  have hstrict := affinePlatform_circleAverage_lt_Catalan k hk
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hcand : (n:ℝ)*(catalan (k-1) : ℝ) ≤
      (n:ℝ)*‖exteriorInverseCoeff F n‖ :=
    mul_le_mul_of_nonneg_left hB hn0
  change (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤ _ at hactual
  change Real.circleAverage
      (fun ζ : ℂ =>
        (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^n) 0 1 <
      (n:ℝ)*(catalan (k-1) : ℝ) at hstrict
  exact (not_lt_of_ge (hcand.trans hactual)) hstrict

end SpringerLean

#print axioms SpringerLean.affinePlatform_circleAverage_lt_Catalan
#print axioms SpringerLean.exteriorOmitted_candidate_second_radius_gt_39_20
