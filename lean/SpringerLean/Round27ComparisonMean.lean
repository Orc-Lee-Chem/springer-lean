import SpringerLean.Round27DoubleCircle

open MeasureTheory Set Metric

namespace SpringerLean

private theorem abs_im_le_norm_sub_real (u : ℂ) (y : ℝ) :
    |u.im| ≤ ‖u - (y : ℂ)‖ := by
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm (u - (y : ℂ))

private theorem im_minus_radius_le_norm_sub_real
    (z u : ℂ) (ρ y : ℝ) (hu : u ∈ closedBall z ρ) :
    |z.im| - ρ ≤ ‖u - (y : ℂ)‖ := by
  have hdist : ‖u - z‖ ≤ ρ := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  have himdiff : |z.im - u.im| ≤ ‖u - z‖ := by
    have h := Complex.abs_im_le_norm (u - z)
    simpa only [Complex.sub_im, abs_sub_comm] using h
  have htri : |z.im| ≤ |u.im| + |z.im - u.im| := by
    calc
      |z.im| = |u.im + (z.im - u.im)| := by ring
      _ ≤ |u.im| + |z.im - u.im| := abs_add_le _ _
  have huim := abs_im_le_norm_sub_real u y
  linarith

/-- The arcsine comparison potential is harmonic in the circle-mean sense
on every disk that stays off the real comparison segment. The proof clips
the logarithmic kernel below by a positive constant, making the double
circle integral jointly continuous before applying Fubini. -/
theorem comparisonSegmentPotential_circleAverage_eq_of_im_radius
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hsep : ρ < |z.im|) :
    Real.circleAverage comparisonSegmentPotential z ρ =
      comparisonSegmentPotential z := by
  let δ : ℝ := |z.im| - ρ
  have hδ : 0 < δ := sub_pos.mpr hsep
  let Y : ℂ → ℂ := fun ζ => ((2 * ζ.re : ℝ) : ℂ)
  let K : ℂ → ℂ → ℝ := fun u ζ => Real.log (max δ ‖u - Y ζ‖)
  have hbase : Continuous (fun p : ℂ × ℂ => ‖p.1 - Y p.2‖) := by
    dsimp [Y]
    fun_prop
  have hmax : Continuous (fun p : ℂ × ℂ => max δ ‖p.1 - Y p.2‖) :=
    continuous_const.max hbase
  have hKcont : Continuous (fun p : ℂ × ℂ => K p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : 0 < max δ ‖p.1 - Y p.2‖ :=
      lt_of_lt_of_le hδ (le_max_left _ _)
    change ContinuousAt (fun p : ℂ × ℂ => Real.log (max δ ‖p.1 - Y p.2‖)) p
    have hlog : ContinuousAt Real.log (max δ ‖p.1 - Y p.2‖) :=
      Real.continuousAt_log (ne_of_gt hp)
    exact ContinuousAt.comp (f := fun q : ℂ × ℂ => max δ ‖q.1 - Y q.2‖)
      (x := p) hlog (hmax.continuousAt (x := p))
  have hcenter (ζ : ℂ) : K z ζ = Real.log ‖z - Y ζ‖ := by
    dsimp [K]
    have hbound : δ ≤ ‖z - Y ζ‖ := by
      have him := abs_im_le_norm_sub_real z (2 * ζ.re)
      dsimp [δ]
      linarith
    rw [max_eq_right hbound]
  have hcircle (u ζ : ℂ) (hu : u ∈ sphere z |ρ|) :
      K u ζ = Real.log ‖u - Y ζ‖ := by
    dsimp [K]
    have huz : u ∈ closedBall z ρ := by
      have hus : dist u z = |ρ| := by simpa only [mem_sphere] using hu
      rw [abs_of_pos hρ] at hus
      exact mem_closedBall.mpr (le_of_eq hus)
    have hbound : δ ≤ ‖u - Y ζ‖ :=
      im_minus_radius_le_norm_sub_real z u ρ (2 * ζ.re) huz
    rw [max_eq_right hbound]
  have hpoint (ζ : ℂ) :
      Real.circleAverage (fun u : ℂ => K u ζ) z ρ = K z ζ := by
    calc
      Real.circleAverage (fun u : ℂ => K u ζ) z ρ =
          Real.circleAverage (fun u : ℂ => Real.log ‖u - Y ζ‖) z ρ := by
            apply Real.circleAverage_congr_sphere
            intro u hu
            exact hcircle u ζ hu
      _ = Real.log ‖z - Y ζ‖ := by
            apply log_norm_sub_circleAverage_eq_of_radius_le z (Y ζ) ρ hρ
            have him := abs_im_le_norm_sub_real z (2 * ζ.re)
            linarith
      _ = K z ζ := (hcenter ζ).symm
  have hinner (u : ℂ) (hu : u ∈ sphere z |ρ|) :
      Real.circleAverage (fun ζ : ℂ => K u ζ) 0 1 = comparisonSegmentPotential u := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    exact hcircle u ζ hu
  calc
    Real.circleAverage comparisonSegmentPotential z ρ =
        Real.circleAverage
          (fun u : ℂ => Real.circleAverage (fun ζ : ℂ => K u ζ) 0 1) z ρ := by
            apply Real.circleAverage_congr_sphere
            intro u hu
            exact (hinner u hu).symm
    _ = Real.circleAverage
          (fun ζ : ℂ => Real.circleAverage (fun u : ℂ => K u ζ) z ρ) 0 1 :=
            circleAverage_circleAverage_comm_of_continuous K hKcont z ρ
    _ = Real.circleAverage (fun ζ : ℂ => K z ζ) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro ζ hζ
          exact hpoint ζ
    _ = comparisonSegmentPotential z := by
          apply Real.circleAverage_congr_sphere
          intro ζ hζ
          exact hcenter ζ

end SpringerLean
