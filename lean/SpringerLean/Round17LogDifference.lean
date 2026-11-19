import SpringerLean.Round17KernelProduct

open MeasureTheory Set

namespace SpringerLean

/-- The horizontal-displacement part of the compensated line logarithm is
integrable for every nonnegative displacement, including zero. -/
theorem verticalLogRadial_sub_one_integrable
    {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun t : ℝ => verticalLogRadial b t - verticalLogRadial 1 t) := by
  let μ : Measure ℝ := volume.restrict (uIoc (1 : ℝ) b)
  haveI : IsFiniteMeasure μ := by
    by_cases h : 1 ≤ b
    · simpa [μ, uIoc_of_le h] using Real.isFiniteMeasure_restrict_Ioc 1 b
    · have h' : b ≤ 1 := le_of_not_ge h
      simpa [μ, uIoc_of_ge h'] using Real.isFiniteMeasure_restrict_Ioc b 1
  have hprod : Integrable (fun p : ℝ × ℝ => p.1 / (p.1 ^ 2 + p.2 ^ 2))
      (μ.prod volume) := by
    by_cases h : 1 ≤ b
    · simpa [μ, uIoc_of_le h] using
        (verticalCauchyKernel_integrable_prod_Ioc (l := (1 : ℝ)) (u := b) (by norm_num))
    · have h' : b ≤ 1 := le_of_not_ge h
      simpa [μ, uIoc_of_ge h'] using
        (verticalCauchyKernel_integrable_prod_Ioc (l := b) (u := (1 : ℝ)) hb)
  have hinner : Integrable
      (fun t : ℝ => ∫ lam : ℝ in uIoc (1 : ℝ) b,
        lam / (lam ^ 2 + t ^ 2)) := by
    simpa only [μ] using hprod.integral_prod_right
  have hinterval : Integrable
      (fun t : ℝ => ∫ lam : ℝ in (1 : ℝ)..b,
        lam / (lam ^ 2 + t ^ 2)) := by
    have hpoint (t : ℝ) :
        (∫ lam : ℝ in (1 : ℝ)..b, lam / (lam ^ 2 + t ^ 2)) =
          (if (1 : ℝ) ≤ b then 1 else -1 : ℝ) *
            (∫ lam : ℝ in uIoc (1 : ℝ) b,
              lam / (lam ^ 2 + t ^ 2)) := by
      simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul]
    convert hinner.const_mul (if (1 : ℝ) ≤ b then 1 else -1 : ℝ) using 1
    funext t
    exact hpoint t
  have hae : (fun t : ℝ => verticalLogRadial b t - verticalLogRadial 1 t) =ᵐ[volume]
      (fun t => ∫ lam : ℝ in (1 : ℝ)..b,
        lam / (lam ^ 2 + t ^ 2)) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by simp [ae_iff, measure_singleton]]
      with t ht
    exact verticalLogRadial_sub_one_eq_intervalIntegral b t ht
  exact hinterval.congr hae.symm

/-- The signed whole-line integral of the radial logarithm difference is
exactly `π (b-1)` for every `b ≥ 0`, including `b=0`. -/
theorem verticalLogRadial_sub_one_integral
    {b : ℝ} (hb : 0 ≤ b) :
    ∫ t : ℝ, (verticalLogRadial b t - verticalLogRadial 1 t) =
      Real.pi * (b - 1) := by
  have hprod : Integrable (fun p : ℝ × ℝ => p.1 / (p.1 ^ 2 + p.2 ^ 2))
      ((volume.restrict (uIoc (1 : ℝ) b)).prod volume) := by
    by_cases h : 1 ≤ b
    · simpa only [uIoc_of_le h] using
        (verticalCauchyKernel_integrable_prod_Ioc (l := (1 : ℝ)) (u := b) (by norm_num))
    · have h' : b ≤ 1 := le_of_not_ge h
      simpa only [uIoc_of_ge h'] using
        (verticalCauchyKernel_integrable_prod_Ioc (l := b) (u := (1 : ℝ)) hb)
  have hswap := (intervalIntegral_integral_swap
    (a := (1 : ℝ)) (b := b)
    (f := fun lam t : ℝ => lam / (lam ^ 2 + t ^ 2)) hprod).symm
  calc
    _ = ∫ t : ℝ, (∫ lam : ℝ in (1 : ℝ)..b,
          lam / (lam ^ 2 + t ^ 2)) := by
      apply integral_congr_ae
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by simp [ae_iff, measure_singleton]]
        with t ht
      exact verticalLogRadial_sub_one_eq_intervalIntegral b t ht
    _ = ∫ lam : ℝ in (1 : ℝ)..b,
          (∫ t : ℝ, lam / (lam ^ 2 + t ^ 2)) := hswap
    _ = ∫ _lam : ℝ in (1 : ℝ)..b, Real.pi := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with lam hlam
      have hpos : 0 < lam := by
        rcases le_total 1 b with h | h
        · rw [uIoc_of_le h] at hlam
          exact lt_trans (by norm_num) hlam.1
        · rw [uIoc_of_ge h] at hlam
          exact lt_of_le_of_lt hb hlam.1
      exact verticalCauchyKernel_integral hpos
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- The pointwise sign of the radial logarithm difference, away from the
single possible logarithmic singularity. -/
theorem verticalLogRadial_sub_one_nonneg_of_one_le
    {b : ℝ} (hb : 1 ≤ b) (t : ℝ) :
    0 ≤ verticalLogRadial b t - verticalLogRadial 1 t := by
  have hpos : 0 < t ^ 2 + (1 : ℝ) ^ 2 := by positivity
  have hle : t ^ 2 + (1 : ℝ) ^ 2 ≤ t ^ 2 + b ^ 2 := by
    nlinarith
  have hlog := Real.log_le_log hpos hle
  norm_num at hlog
  dsimp [verticalLogRadial]
  linarith

theorem verticalLogRadial_sub_one_nonpos_of_le_one
    {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    {t : ℝ} (ht : t ≠ 0) :
    verticalLogRadial b t - verticalLogRadial 1 t ≤ 0 := by
  have hpos : 0 < t ^ 2 + b ^ 2 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    positivity
  have hle : t ^ 2 + b ^ 2 ≤ t ^ 2 + (1 : ℝ) ^ 2 := by
    nlinarith
  have hlog := Real.log_le_log hpos hle
  norm_num at hlog
  dsimp [verticalLogRadial]
  linarith

/-- Exact L¹ norm of the radial logarithm difference, for all `b≥0`. -/
theorem verticalLogRadial_sub_one_abs_integral
    {b : ℝ} (hb : 0 ≤ b) :
    ∫ t : ℝ, |verticalLogRadial b t - verticalLogRadial 1 t| =
      Real.pi * |b - 1| := by
  by_cases h : 1 ≤ b
  · have hpoint (t : ℝ) :
        |verticalLogRadial b t - verticalLogRadial 1 t| =
          verticalLogRadial b t - verticalLogRadial 1 t :=
      abs_of_nonneg (verticalLogRadial_sub_one_nonneg_of_one_le h t)
    simp_rw [hpoint, verticalLogRadial_sub_one_integral hb,
      abs_of_nonneg (sub_nonneg.mpr h)]
  · have hb1 : b ≤ 1 := le_of_not_ge h
    have hae : (fun t : ℝ => |verticalLogRadial b t - verticalLogRadial 1 t|) =ᵐ[volume]
        (fun t => -(verticalLogRadial b t - verticalLogRadial 1 t)) := by
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by simp [ae_iff, measure_singleton]]
        with t ht
      exact abs_of_nonpos (verticalLogRadial_sub_one_nonpos_of_le_one hb hb1 ht)
    rw [integral_congr_ae hae, integral_neg, verticalLogRadial_sub_one_integral hb,
      abs_of_nonpos (sub_nonpos.mpr hb1)]
    ring

end SpringerLean
