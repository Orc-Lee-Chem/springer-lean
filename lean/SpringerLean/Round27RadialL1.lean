import SpringerLean.Round27Tail

open MeasureTheory Set Filter

namespace SpringerLean

/-- The exact L¹ distance between two radial vertical logarithms. The
pointwise ordering may fail at the single point `t=0` when a radius is zero;
the Lebesgue integral is unaffected. -/
theorem verticalLogRadial_sub_abs_integral
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (∫ t : ℝ, |verticalLogRadial b t - verticalLogRadial c t|) =
      Real.pi * |b - c| := by
  have hbInt := verticalLogRadial_sub_one_integrable hb
  have hcInt := verticalLogRadial_sub_one_integrable hc
  have hdiff : Integrable (fun t : ℝ =>
      verticalLogRadial b t - verticalLogRadial c t) := by
    convert hbInt.sub hcInt using 1
    funext t
    change verticalLogRadial b t - verticalLogRadial c t =
      (verticalLogRadial b t - verticalLogRadial 1 t) -
        (verticalLogRadial c t - verticalLogRadial 1 t)
    ring
  have hsigned : (∫ t : ℝ,
      verticalLogRadial b t - verticalLogRadial c t) =
      Real.pi * (b - c) := by
    calc
      _ = ∫ t : ℝ, (verticalLogRadial b t - verticalLogRadial 1 t) -
            (verticalLogRadial c t - verticalLogRadial 1 t) := by
              congr 1
              funext t
              ring
      _ = (∫ t : ℝ, verticalLogRadial b t - verticalLogRadial 1 t) -
            (∫ t : ℝ, verticalLogRadial c t - verticalLogRadial 1 t) :=
              integral_sub hbInt hcInt
      _ = _ := by rw [verticalLogRadial_sub_one_integral hb,
        verticalLogRadial_sub_one_integral hc]; ring
  have hsign {x y : ℝ} (hxy : x ≤ y) (hx0 : 0 ≤ x) {t : ℝ} (ht : t ≠ 0) :
      verticalLogRadial x t ≤ verticalLogRadial y t := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hpos : 0 < t ^ 2 + x ^ 2 := by positivity
    have hle : t ^ 2 + x ^ 2 ≤ t ^ 2 + y ^ 2 := by nlinarith
    have hlog := Real.log_le_log hpos hle
    dsimp [verticalLogRadial]
    linarith
  by_cases hbc : c ≤ b
  · have hae : (fun t : ℝ => |verticalLogRadial b t - verticalLogRadial c t|) =ᵐ[volume]
        (fun t => verticalLogRadial b t - verticalLogRadial c t) := by
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by simp [ae_iff, measure_singleton]]
        with t ht
      exact abs_of_nonneg (sub_nonneg.mpr (hsign hbc hc ht))
    rw [integral_congr_ae hae, hsigned, abs_of_nonneg (sub_nonneg.mpr hbc)]
  · have hcb : b ≤ c := le_of_not_ge hbc
    have hae : (fun t : ℝ => |verticalLogRadial b t - verticalLogRadial c t|) =ᵐ[volume]
        (fun t => -(verticalLogRadial b t - verticalLogRadial c t)) := by
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by simp [ae_iff, measure_singleton]]
        with t ht
      exact abs_of_nonpos (sub_nonpos.mpr (hsign hcb hb ht))
    rw [integral_congr_ae hae, integral_neg, hsigned,
      abs_of_nonpos (sub_nonpos.mpr hcb)]
    ring

end SpringerLean