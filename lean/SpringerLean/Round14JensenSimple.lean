import SpringerLean.Round14PotentialBoundary

open MeasureTheory Metric

namespace SpringerLean

/-- Jensen's formula with exactly one simple zero in the closed unit disk.
The simple-zero premise is explicit, so this is an intermediate analytic lemma. -/
theorem circleAverage_log_norm_of_unique_simple_zero
    (f : ℂ → ℂ)
    (hAnal : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0)
    (u₀ : ℂ) (hu₀ : ‖u₀‖ < 1)
    (hzero : f u₀ = 0)
    (hsimple : deriv f u₀ ≠ 0)
    (hunique : ∀ u : ℂ, ‖u‖ ≤ 1 → f u = 0 → u = u₀) :
    Real.circleAverage (fun u : ℂ => Real.log ‖f u‖) 0 1 =
      Real.log ‖f 0‖ - Real.log ‖u₀‖ := by
  have hAnal' : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |(1 : ℝ)|) := by
    simpa only [abs_one] using hAnal
  have hJ := hAnal'.circleAverage_log_norm
    (R := (1 : ℝ)) (c := (0 : ℂ)) (by norm_num) hf0
  norm_num at hJ
  have hterm (u : ℂ) (hne : u ≠ u₀) :
      -((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u : ℝ) *
        Real.log ‖u‖) = 0 := by
    by_cases hu : u ∈ closedBall (0 : ℂ) |(1 : ℝ)|
    · have hle : ‖u‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right, abs_one] using hu
      have hnot : f u ≠ 0 := by
        intro hz
        exact hne (hunique u hle hz)
      have horder : analyticOrderAt f u = 0 :=
        ((hAnal' u hu).analyticOrderAt_eq_zero).mpr hnot
      rw [MeromorphicOn.divisor_apply hAnal'.meromorphicOn hu,
        (hAnal' u hu).meromorphicOrderAt_eq, horder]
      simp
    · have hdiv : MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u = 0 := by
        have hu' : u ∉ closedBall (0 : ℂ) 1 := by simpa using hu
        rw [MeromorphicOn.divisor_def]
        simp [hu']
      rw [hdiv]
      simp
  have hsum :
      (∑ᶠ u : ℂ, -((MeromorphicOn.divisor f (closedBall (0 : ℂ) |(1 : ℝ)|) u : ℝ) *
        Real.log ‖u‖)) = -Real.log ‖u₀‖ := by
    rw [finsum_eq_single _ u₀ hterm]
    have hu₀mem : u₀ ∈ closedBall (0 : ℂ) |(1 : ℝ)| := by
      simpa only [mem_closedBall, dist_zero_right, abs_one] using hu₀.le
    have horder : analyticOrderAt f u₀ = 1 :=
      (hAnal' u₀ hu₀mem).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
        hzero hsimple
    rw [MeromorphicOn.divisor_apply hAnal'.meromorphicOn hu₀mem,
      (hAnal' u₀ hu₀mem).meromorphicOrderAt_eq, horder]
    simp
  rw [hsum] at hJ
  simpa only [sub_eq_add_neg, add_comm] using hJ

/-- The exact image-value potential follows once the unique reciprocal
zero is shown simple. This exposes the remaining univalence-to-derivative bridge. -/
theorem regularExterior_image_boundary_log_potential_of_simple_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk)
    (hsimple : deriv
      (regularBoundaryPotential s F (rescaleExterior s F v)) v⁻¹ ≠ 0) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = Real.log ‖v‖ := by
  let q := regularBoundaryPotential s F (rescaleExterior s F v)
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num [exteriorDisk] at hv
  have hu : ‖v⁻¹‖ < 1 := by
    rw [norm_inv]
    exact (inv_lt_one₀ (by have : 0 < ‖v‖ := norm_pos_iff.mpr hv0; exact this)).mpr hv
  have hJ := circleAverage_log_norm_of_unique_simple_zero q
    (regularBoundaryPotential_analytic_closedDisk F hc hs0 hs1 _)
    (by simp [q]) v⁻¹ hu
    (regularBoundaryPotential_zero_of_image F hs0 hv) hsimple
    (fun u hu' hz =>
      regularBoundaryPotential_zero_unique_of_image_closedDisk F hc hs0 hs1 hv hu' hz)
  calc
    _ = Real.circleAverage (fun u : ℂ => Real.log ‖q u‖) 0 1 :=
      regularExterior_boundary_log_potential_eq_factor F hs0 _
    _ = Real.log ‖q 0‖ - Real.log ‖v⁻¹‖ := hJ
    _ = Real.log ‖v‖ := by simp [q, norm_inv, Real.log_inv]

end SpringerLean
