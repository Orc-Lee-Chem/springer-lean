import SpringerLean.Round1335CoarseTwoPointScalar
import SpringerLean.Round615TwoPointConvexHull

open scoped ComplexConjugate

namespace SpringerLean

/-- Complex cosine rule with the endpoint direction normalized explicitly. -/
theorem complex_chord_projection_identity
    (w P ξ : ℂ) (R : ℝ) (hξ : ‖ξ‖ = 1)
    (hP : P = ξ * (R : ℂ)) :
    ‖w - P‖ ^ 2 = R ^ 2 + ‖w‖ ^ 2 - 2 * R * (conj ξ * w).re := by
  have hξsq : ξ.re ^ 2 + ξ.im ^ 2 = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hξ
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    nlinarith
  rw [hP]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.conj_re,
    Complex.conj_im]
  nlinarith [hξsq]

/-- The two-point hull estimate gives a `17e/4` chord alternative for any
actual pair of hull points, uniformly at `e ≤ 1/20`. -/
theorem exteriorOmitted_hull_near_far_17_4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (w P : ℂ)
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    {e : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ 1/20)
    (hwr : 2 - e ≤ ‖w‖) (hPr : 2 - e ≤ ‖P‖) :
    ‖w - P‖ ≤ (17/4 : ℝ) * e ∨
      4 - ‖w - P‖ ≤ (17/4 : ℝ) * e := by
  have hpair := exteriorOmitted_pair_distance_deficit F hc w P
    hw hP he0 (by linarith) hwr hPr
  have hnormw : ‖w‖ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have hnormP : ‖P‖ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hP
  have hu4 : ‖w - P‖ ≤ 4 := by
    calc
      ‖w - P‖ ≤ ‖w‖ + ‖P‖ := norm_sub_le _ _
      _ ≤ 4 := by linarith
  apply twoPoint_near_far_17_4 he0 heδ (norm_nonneg _) hu4
  nlinarith [sq_nonneg e]

/-- On the forward half of a real omitted endpoint, every high-radius
hull point satisfies the same `e+5e²` projection deficit. -/
theorem exteriorOmitted_forward_half_projection_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P w : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hPbig : (39/20 : ℝ) ≤ ‖P‖)
    (hwr : (39/20 : ℝ) ≤ ‖w‖)
    (hmax : ‖w‖ ≤ ‖P‖)
    (hforward : 0 ≤ (conj (P/(‖P‖ : ℂ))*w).re) :
    let e : ℝ := 2 - ‖w‖
    2 - (conj (P/(‖P‖ : ℂ))*w).re ≤ e + 5 * e ^ 2 := by
  dsimp only
  let R : ℝ := ‖P‖
  let e : ℝ := 2 - ‖w‖
  let ξ : ℂ := P/(R : ℂ)
  have hP2 : R ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hP
  have hw2 : ‖w‖ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc hw
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have heδ : e ≤ 1/20 := by dsimp [e]; linarith
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hP0 : P ≠ 0 := by
    intro hp
    rw [hp, norm_zero] at hPbig
    norm_num at hPbig
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ, R]
    simp [hP0]
  have hPform : P = ξ*(R : ℂ) := by
    dsimp [ξ]
    field_simp [hR0,hP0]
  have hcos := complex_chord_projection_identity w P ξ R hξ hPform
  have hwr0 : 2 - e ≤ ‖w‖ := by dsimp [e]; linarith
  have hPr0 : 2 - e ≤ ‖P‖ := by dsimp [e]; linarith
  have hpair := exteriorOmitted_pair_distance_deficit F hc w P
    hw hP he0 (by linarith) hwr0 hPr0
  have hu0 : 0 ≤ ‖w-P‖ := norm_nonneg _
  have hu4 : ‖w-P‖ ≤ 4 := by
    calc
      ‖w-P‖ ≤ ‖w‖+‖P‖ := norm_sub_le _ _
      _ ≤ 4 := by dsimp [R] at hP2; linarith
  have hforward8 : ‖w-P‖ ^ 2 ≤ 8 := by
    have hproj : 0 ≤ 2*R*(conj ξ*w).re := by
      apply mul_nonneg (by linarith)
      exact hforward
    have hRsq : R ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2-R)]
    have hwsq : ‖w‖ ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2-‖w‖)]
    nlinarith [hcos]
  have hnear : ‖w-P‖ ≤ (17/4 : ℝ)*e :=
    twoPoint_forward_half_near_17_4 he0 heδ hu0 hu4
      (by nlinarith [sq_nonneg e]) hforward8
  have hcos' : ‖w-P‖ ^ 2 = R ^ 2 + (2-e) ^ 2 -
      2*R*(conj ξ*w).re := by
    convert hcos using 1 <;> dsimp [e] <;> ring
  have hproj := nearChord_projection_deficit_five hPbig he0 heδ
    hu0 hnear hcos' (by dsimp [e,R]; linarith)
  simpa only [ξ, R, e] using hproj

end SpringerLean

#print axioms SpringerLean.complex_chord_projection_identity
#print axioms SpringerLean.exteriorOmitted_hull_near_far_17_4
#print axioms SpringerLean.exteriorOmitted_forward_half_projection_five
