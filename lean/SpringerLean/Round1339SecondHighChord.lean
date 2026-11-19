import SpringerLean.Round1338OppositeHalfGeometry

open scoped ComplexConjugate

namespace SpringerLean

/-- Two points in the selected opposite half are close to one another
when both have radius at least `39/20` and one is the half-plane radius
maximizer. This is the geometric part of the second-end model bound. -/
theorem exteriorOmitted_opposite_half_second_near
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w ξ₁ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ₁ : ‖ξ₁‖ = 1)
    (hP₁form : P₁ = ξ₁*(‖P₁‖ : ℂ))
    (hP₁big : (39/20 : ℝ) ≤ ‖P₁‖)
    (hP₂big : (39/20 : ℝ) ≤ ‖P₂‖)
    (hwr : (39/20 : ℝ) ≤ ‖w‖)
    (hP₁maxw : ‖w‖ ≤ ‖P₁‖)
    (hP₁maxP₂ : ‖P₂‖ ≤ ‖P₁‖)
    (hP₂maxw : ‖w‖ ≤ ‖P₂‖)
    (hnegw : (conj ξ₁*w).re ≤ 0)
    (hnegP₂ : (conj ξ₁*P₂).re ≤ 0) :
    let e : ℝ := 2 - ‖w‖
    ‖w-P₂‖ ≤ (17/4 : ℝ)*e := by
  dsimp only
  let e : ℝ := 2 - ‖w‖
  let d₂ : ℝ := 2 - ‖P₂‖
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hP₂2 := exteriorOmitted_convexHull_norm_le_two F hc hP₂
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/20 := by dsimp [e]; linarith
  have hd0 : 0 ≤ d₂ := by dsimp [d₂]; linarith
  have hdδ : d₂ ≤ 1/20 := by dsimp [d₂]; linarith
  have hde : d₂ ≤ e := by dsimp [d₂,e]; linarith
  have hwFar := (exteriorOmitted_opposite_half_far_17_4
    F hc P₁ w ξ₁ hP₁ hw hξ₁ hP₁form hP₁big hwr
    hP₁maxw hnegw).2
  have hP₂Far := (exteriorOmitted_opposite_half_far_17_4
    F hc P₁ P₂ ξ₁ hP₁ hP₂ hξ₁ hP₁form hP₁big hP₂big
    hP₁maxP₂ hnegP₂).2
  have hsum : ‖w-P₂‖ ≤ ‖w+P₁‖+‖P₂+P₁‖ := by
    have hid : w-P₂ = (w+P₁)-(P₂+P₁) := by ring
    rw [hid]
    exact norm_sub_le _ _
  have hchordSq : ‖w-P₂‖^2 ≤ 68*e := by
    have haux : (‖w+P₁‖+‖P₂+P₁‖)^2 ≤
        2*‖w+P₁‖^2+2*‖P₂+P₁‖^2 := by
      nlinarith [sq_nonneg (‖w+P₁‖-‖P₂+P₁‖)]
    have hmono := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsum
    nlinarith [haux, hwFar, hP₂Far]
  rcases exteriorOmitted_hull_near_far_17_4 F hc w P₂ hw hP₂
      he0 heδ (by dsimp [e]; linarith)
      (by dsimp [e]; linarith) with hnear | hfar
  · exact hnear
  · have hlarge : (303/80 : ℝ) ≤ ‖w-P₂‖ := by linarith
    nlinarith [hchordSq, sq_nonneg (‖w-P₂‖-303/80)]

/-- After the first-end far-chord argument, the selected second end has
exactly the same `e+5e²` projection model on its assigned high-radius
half-plane. The two-end radius premise is explicit here. -/
theorem exteriorOmitted_opposite_half_second_projection_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w ξ₁ ξ₂ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ₁ : ‖ξ₁‖ = 1) (hξ₂ : ‖ξ₂‖ = 1)
    (hP₁form : P₁ = ξ₁*(‖P₁‖ : ℂ))
    (hP₂form : P₂ = ξ₂*(‖P₂‖ : ℂ))
    (hP₁big : (39/20 : ℝ) ≤ ‖P₁‖)
    (hP₂big : (39/20 : ℝ) ≤ ‖P₂‖)
    (hwr : (39/20 : ℝ) ≤ ‖w‖)
    (hP₁maxw : ‖w‖ ≤ ‖P₁‖)
    (hP₁maxP₂ : ‖P₂‖ ≤ ‖P₁‖)
    (hP₂maxw : ‖w‖ ≤ ‖P₂‖)
    (hnegw : (conj ξ₁*w).re ≤ 0)
    (hnegP₂ : (conj ξ₁*P₂).re ≤ 0) :
    let e : ℝ := 2 - ‖w‖
    2 - (conj ξ₂*w).re ≤ e+5*e^2 := by
  dsimp only
  let e : ℝ := 2 - ‖w‖
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/20 := by dsimp [e]; linarith
  have hnear := exteriorOmitted_opposite_half_second_near
    F hc P₁ P₂ w ξ₁ hP₁ hP₂ hw hξ₁ hP₁form hP₁big hP₂big
    hwr hP₁maxw hP₁maxP₂ hP₂maxw hnegw hnegP₂
  have hcos := complex_chord_projection_identity w P₂ ξ₂ ‖P₂‖ hξ₂ hP₂form
  have hcos' : ‖w-P₂‖^2 = ‖P₂‖^2+(2-e)^2-
      2*‖P₂‖*(conj ξ₂*w).re := by
    convert hcos using 1 <;> dsimp [e] <;> ring
  exact nearChord_projection_deficit_five hP₂big he0 heδ
    (norm_nonneg _) hnear hcos' (by linarith [hP₂maxw])

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_opposite_half_second_near
#print axioms SpringerLean.exteriorOmitted_opposite_half_second_projection_five
