import SpringerLean.Round615TwoPointConvexHull

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- The cutting line is uniformly below the proposed opposite endpoint
radius once the first actual hull radius is at least1.896. All constants
are exact rationals. -/
theorem exteriorOmitted_cutting_line_norm_lt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (P w : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hPr : (237 : ℝ) / 125 ≤ ‖P‖)
    (horth : (conj P * w).re = 0) : ‖w‖ < (8 : ℝ) / 5 := by
  have hn (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply,pow_two] using Complex.sq_norm z
  have ho : P.re * w.re + P.im * w.im = 0 := by
    simpa only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add] using horth
  have hminus : ‖w - P‖ ^ 2 = ‖w‖ ^ 2 + ‖P‖ ^ 2 := by
    have hm := hn (w - P)
    simp only [Complex.sub_re,Complex.sub_im] at hm
    nlinarith [hn w,hn P]
  have hplus : ‖w + P‖ ^ 2 = ‖w‖ ^ 2 + ‖P‖ ^ 2 := by
    have hm := hn (w + P)
    simp only [Complex.add_re,Complex.add_im] at hm
    nlinarith [hn w,hn P]
  have ht := exteriorOmitted_convexHull_two_point F hc w P hw hP
  rw [hplus, ← hminus] at ht
  by_contra hbad
  have hwlow : (8 : ℝ) / 5 ≤ ‖w‖ := le_of_not_gt hbad
  have hp2 : ((237 : ℝ) / 125) ^ 2 ≤ ‖P‖ ^ 2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg P)).mpr hPr
  have hw2 : ((8 : ℝ) / 5) ^ 2 ≤ ‖w‖ ^ 2 :=
    (sq_le_sq₀ (by norm_num) (norm_nonneg w)).mpr hwlow
  have hd2 : ((62 : ℝ) / 25) ^ 2 < ‖w - P‖ ^ 2 := by nlinarith
  have hd : (62 : ℝ) / 25 < ‖w - P‖ := by nlinarith [norm_nonneg (w - P)]
  nlinarith

theorem exteriorOmitted_negative_half_direction_strict
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (P w : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hw : w ∈ convexHull ℝ (exteriorOmitted F))
    (hPr : (237 : ℝ) / 125 ≤ ‖P‖)
    (hwr : (8 : ℝ) / 5 ≤ ‖w‖) (hneg : (conj P * w).re ≤ 0) :
    (conj P * w).re < 0 := by
  apply lt_of_le_of_ne hneg
  intro he
  exact (exteriorOmitted_cutting_line_norm_lt F hc P w hP hw hPr he).not_ge hwr

end SpringerLean
