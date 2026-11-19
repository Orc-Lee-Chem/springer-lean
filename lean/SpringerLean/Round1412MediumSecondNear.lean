import SpringerLean.Round1411MediumOppositeFar

open scoped ComplexConjugate

namespace SpringerLean

/-- A radius-maximal point in the opposite half is close to every
assigned point of radius at least 1.9, using the same 0.1 dichotomy. -/
theorem exteriorOmitted_opposite_half_second_near_451_100
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P₁ P₂ w ξ₁ : ℂ)
    (hP₁ : P₁ ∈ convexHull ℝ (exteriorOmitted F))
    (hP₂ : P₂ ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hξ₁ : ‖ξ₁‖ = 1)
    (hP₁form : P₁ = ξ₁*(‖P₁‖:ℂ))
    (hP₁big : (19/10 : ℝ) ≤ ‖P₁‖)
    (hP₂big : (19/10 : ℝ) ≤ ‖P₂‖)
    (hwr : (19/10 : ℝ) ≤ ‖w‖)
    (hP₁maxw : ‖w‖ ≤ ‖P₁‖)
    (hP₁maxP₂ : ‖P₂‖ ≤ ‖P₁‖)
    (hP₂maxw : ‖w‖ ≤ ‖P₂‖)
    (hnegw : (conj ξ₁*w).re ≤ 0)
    (hnegP₂ : (conj ξ₁*P₂).re ≤ 0) :
    let e : ℝ := 2-‖w‖
    ‖w-P₂‖ ≤ (451/100 : ℝ)*e := by
  dsimp only
  let e : ℝ := 2-‖w‖
  let d₂ : ℝ := 2-‖P₂‖
  have hw2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hP₂2 := exteriorOmitted_convexHull_norm_le_two F hc hP₂
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/10 := by dsimp [e]; linarith
  have hd0 : 0 ≤ d₂ := by dsimp [d₂]; linarith
  have hde : d₂ ≤ e := by dsimp [d₂,e]; linarith
  have hwFar := (exteriorOmitted_opposite_half_far_451_100
    F hc P₁ w ξ₁ hP₁ hw hξ₁ hP₁form hP₁big hwr hP₁maxw hnegw).2
  have hP₂Far := (exteriorOmitted_opposite_half_far_451_100
    F hc P₁ P₂ ξ₁ hP₁ hP₂ hξ₁ hP₁form hP₁big hP₂big
    hP₁maxP₂ hnegP₂).2
  have hsum : ‖w-P₂‖ ≤ ‖w+P₁‖+‖P₂+P₁‖ := by
    have hid : w-P₂=(w+P₁)-(P₂+P₁) := by ring
    rw [hid]
    exact norm_sub_le _ _
  have hchordSq : ‖w-P₂‖^2 ≤ 16*(451/100 : ℝ)*e := by
    have haux : (‖w+P₁‖+‖P₂+P₁‖)^2 ≤
        2*‖w+P₁‖^2+2*‖P₂+P₁‖^2 := by
      nlinarith [sq_nonneg (‖w+P₁‖-‖P₂+P₁‖)]
    have hmono := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsum
    nlinarith [haux,hwFar,hP₂Far]
  have hpair := exteriorOmitted_pair_distance_deficit F hc w P₂
    hw hP₂ he0 (by linarith) (by dsimp [e]; linarith)
    (by dsimp [e]; linarith)
  have hpair' : ‖w-P₂‖*(4-‖w-P₂‖) ≤ 16*e := by
    nlinarith [sq_nonneg e]
  have hu4 : ‖w-P₂‖ ≤ 4 := by
    calc
      ‖w-P₂‖ ≤ ‖w‖+‖P₂‖ := norm_sub_le _ _
      _ ≤ 4 := by linarith
  exact twoPoint_second_near_of_sq_451_100 he0 heδ
    (norm_nonneg _) hu4 hpair' hchordSq

/-- A near chord at radius at least 1.9 has positive projection in
the selected endpoint direction. -/
theorem medium_near_endpoint_projection_nonneg
    (P w ξ : ℂ)
    (hξ : ‖ξ‖ = 1)
    (hPform : P=ξ*(‖P‖:ℂ))
    (hPbig : (19/10 : ℝ) ≤ ‖P‖)
    (hwr : (19/10 : ℝ) ≤ ‖w‖)
    (he : 2-‖w‖ ≤ (1/10 : ℝ))
    (he0 : 0 ≤ 2-‖w‖)
    (hnear : ‖w-P‖ ≤ (451/100 : ℝ)*(2-‖w‖)) :
    0 ≤ (conj ξ*w).re := by
  have hcos := complex_chord_projection_identity w P ξ ‖P‖ hξ hPform
  have hu0 : 0 ≤ ‖w-P‖ := norm_nonneg _
  have husmall : ‖w-P‖ ≤ (451/1000 : ℝ) := by nlinarith
  have husq : ‖w-P‖^2 ≤ (451/1000 : ℝ)^2 :=
    (sq_le_sq₀ hu0 (by norm_num)).mpr husmall
  have hR2 : (19/10 : ℝ)^2 ≤ ‖P‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg P)).mpr hPbig
  have hw2 : (19/10 : ℝ)^2 ≤ ‖w‖^2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg w)).mpr hwr
  nlinarith [hcos,husq,hR2,hw2, norm_nonneg P]

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_opposite_half_second_near_451_100
#print axioms SpringerLean.medium_near_endpoint_projection_nonneg
