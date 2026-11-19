import SpringerLean.Round1336CoarseActualGeometry
import SpringerLean.Round663ActualConvexCaps

open scoped ComplexConjugate

namespace SpringerLean

/-- The already proved near-chord estimate yields a simple affine
radial cap on the high-radius forward half. -/
theorem nearChord_affine_cap
    {e x : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1/20)
    (hproj : 2-x ≤ e+5*e^2) :
    2-e ≤ (2/5 : ℝ)+(4/5)*x := by
  have he2 : 5*e^2 ≤ e/4 := by nlinarith [mul_nonneg he0 (show 0 ≤ 1/20-e by linarith)]
  nlinarith

/-- The coarse single-end profile is globally convex, so the actual
finite-cap projection comparison can use it without any extension lemma. -/
theorem affinePlatformPower_convexOn (n : ℕ) :
    ConvexOn ℝ Set.univ
      (fun x : ℝ => (max (39/20 : ℝ) ((2/5)+(4/5)*x))^n) := by
  have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => (4/5 : ℝ)*x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    dsimp
    apply le_of_eq
    ring
  have haff : ConvexOn ℝ Set.univ (fun x : ℝ => (2/5 : ℝ)+(4/5)*x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    dsimp
    apply le_of_eq
    calc
      (2/5 : ℝ)+(4/5)*(a*x+b*y) =
          (a+b)*(2/5)+(4/5)*(a*x+b*y) := by rw [hab]; ring
      _ = a*((2/5)+(4/5)*x)+b*((2/5)+(4/5)*y) := by ring
  have hmax : ConvexOn ℝ Set.univ
      (fun x : ℝ => max (39/20 : ℝ) ((2/5)+(4/5)*x)) := by
    convert (convexOn_const (39/20 : ℝ) convex_univ).sup haff using 1
  convert (hmax.pow (fun x _ =>
      le_trans (by norm_num : (0:ℝ) ≤ 39/20) (le_max_left _ _)) n) using 1

/-- If the selected opposite-half radius is at most `39/20`, one
globally defined convex-profile *candidate* controls the whole actual
ordinary convex hull. The global convexity and circle integral of its
power are separate analytic steps. -/
theorem exteriorOmitted_first_affine_radius_cap
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w ξ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ : ‖ξ‖ = 1)
    (hP₁norm : P₁ = ξ * (‖P₁‖ : ℂ))
    (hP₁big : (39/20 : ℝ) ≤ ‖P₁‖)
    (hP₁max : ‖w‖ ≤ ‖P₁‖)
    (hP₂small : ‖P₂‖ ≤ (39/20 : ℝ))
    (hP₂max : ∀ z ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*z).re ≤ 0 → ‖z‖ ≤ ‖P₂‖) :
    ‖w‖ ≤ max (39/20 : ℝ) ((2/5)+(4/5)*(conj ξ*w).re) := by
  let x : ℝ := (conj ξ*w).re
  by_cases hsmall : ‖w‖ ≤ (39/20 : ℝ)
  · exact hsmall.trans (le_max_left _ _)
  · by_cases hx : x ≤ 0
    · exact ((hP₂max w hw hx).trans hP₂small).trans (le_max_left _ _)
    · have hwr : (39/20 : ℝ) ≤ ‖w‖ := le_of_lt (lt_of_not_ge hsmall)
      let e : ℝ := 2-‖w‖
      have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
      have he0 : 0 ≤ e := by dsimp [e]; linarith
      have he : e ≤ 1/20 := by dsimp [e]; linarith
      have hR0 : (‖P₁‖ : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 39/20) hP₁big))
      have hξeq : P₁/(‖P₁‖ : ℂ) = ξ := by
        calc
          P₁/(‖P₁‖ : ℂ) = (ξ*(‖P₁‖ : ℂ))/(‖P₁‖ : ℂ) :=
            congrArg (fun z : ℂ => z/(‖P₁‖ : ℂ)) hP₁norm
          _ = ξ := by field_simp
      have hforward : 0 ≤ (conj (P₁/(‖P₁‖ : ℂ))*w).re := by
        rw [hξeq]
        exact le_of_lt (lt_of_not_ge hx)
      have hp := exteriorOmitted_forward_half_projection_five
        F hc P₁ w hP₁ hw hP₁big hwr hP₁max hforward
      rw [hξeq] at hp
      have haff := nearChord_affine_cap he0 he hp
      have hrad : ‖w‖ ≤ (2/5 : ℝ)+(4/5)*x := by
        dsimp [e] at haff
        linarith
      exact hrad.trans (le_max_right _ _)

/-- The coarse one-sided geometry already reaches the original inverse
coefficient by the actual-map convex cap theorem. Only the explicit
comparison-circle cost remains before the `R₂ > 39/20` contradiction. -/
theorem exteriorInverseCoeff_le_affinePlatform_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n) (P₁ P₂ ξ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hξ : ‖ξ‖ = 1)
    (hP₁norm : P₁ = ξ * (‖P₁‖ : ℂ))
    (hP₁big : (39/20 : ℝ) ≤ ‖P₁‖)
    (hP₁max : ∀ w ∈ convexHull ℝ (exteriorOmitted F), ‖w‖ ≤ ‖P₁‖)
    (hP₂small : ‖P₂‖ ≤ (39/20 : ℝ))
    (hP₂max : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 0 → ‖w‖ ≤ ‖P₂‖) :
    (n:ℝ)*‖exteriorInverseCoeff F n‖ ≤
      Real.circleAverage
        (fun ζ : ℂ =>
          (max (39/20 : ℝ) ((2/5)+(4/5)*(2*ζ.re)))^n) 0 1 := by
  have hcap : ∀ w ∈ exteriorOmitted F,
      ‖w‖^n ≤ (max (39/20 : ℝ) ((2/5)+(4/5)*(conj ξ*w).re))^n := by
    intro w hw
    have hwHull : w ∈ convexHull ℝ (exteriorOmitted F) := subset_convexHull ℝ _ hw
    exact pow_le_pow_left₀ (norm_nonneg w)
      (exteriorOmitted_first_affine_radius_cap F hc P₁ P₂ w ξ
        hP₁ hwHull hξ hP₁norm hP₁big (hP₁max w hwHull)
        hP₂small hP₂max) _
  have h := exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps
    (S := {()}) F hc n hn (fun _ : Unit => ξ)
    (by simp [hξ])
    (fun _ : Unit => fun x : ℝ =>
      (max (39/20 : ℝ) ((2/5)+(4/5)*x))^n)
    (by intro i hi; exact affinePlatformPower_convexOn n)
    0 (by simpa using hcap)
  simpa using h

end SpringerLean

#print axioms SpringerLean.nearChord_affine_cap
#print axioms SpringerLean.affinePlatformPower_convexOn
#print axioms SpringerLean.exteriorOmitted_first_affine_radius_cap
#print axioms SpringerLean.exteriorInverseCoeff_le_affinePlatform_cost
