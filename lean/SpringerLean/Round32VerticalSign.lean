import SpringerLean.Round32StrictCircle
import SpringerLean.Round29AuxInfinity
import SpringerLean.Round22BoundarySlope

open MeasureTheory Set Metric

namespace SpringerLean

/-- The actual compensated vertical potential difference is nonpositive at
every threshold. This uses the local circle submean, infinity estimate, and
the already proved one-sided boundary slope of the same actual auxiliary. -/
theorem regularExterior_vertical_potential_difference_integral_nonpos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a : ℝ) :
    (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ a t) ≤ 0 := by
  let u : ℂ → ℝ := fun z => regularVerticalAuxiliary F s ξ z.re z.im
  have hboundary (x : ℝ) :
      u (x : ℂ) =
        ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ x t := by
    simp only [u, Complex.ofReal_re, Complex.ofReal_im]
    exact regularVerticalAuxiliary_boundary F s ξ x
  by_contra hnot
  have hm : 0 < u (a : ℂ) := by
    rw [hboundary]
    exact lt_of_not_ge hnot
  let m : ℝ := u (a : ℂ)
  obtain ⟨R₀, hR₀, hfar⟩ :=
    regularVerticalAuxiliary_infinity_limsup_le_zero
      F hc hs0 hs1 ξ hξ (m / 4) (by dsimp [m]; positivity)
  let R : ℝ := max R₀ (|a| + 1) + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left R₀ (|a|+1)]
  have hR₀R : R₀ ≤ R := by dsimp [R]; linarith [le_max_left R₀ (|a|+1)]
  have haR : |a| < R := by dsimp [R]; linarith [le_max_right R₀ (|a|+1)]
  let D : ℝ := R + R^2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let p : ℝ := m / (16 * D)
  have hp : 0 < p := by dsimp [p]; positivity
  have hpD : p * D = m / 16 := by
    dsimp [p]
    field_simp
  have hpBound : p * (R + R^2) < m / 4 := by
    calc
      p * (R + R^2) < p * D := by
        apply mul_lt_mul_of_pos_left _ hp
        dsimp [D]
        linarith
      _ = m / 16 := hpD
      _ < m / 4 := by linarith
  let V : ℂ → ℝ := fun z => u z + p * z.im + p * z.im^2
  let K : Set ℂ := closedBall 0 R ∩ {z : ℂ | 0 ≤ z.im}
  have hclosed : IsClosed {z : ℂ | 0 ≤ z.im} := by
    exact isClosed_Ici.preimage (by fun_prop : Continuous (fun z : ℂ => z.im))
  have hcompact : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) R).inter_right hclosed
  have haK : (a : ℂ) ∈ K := by
    constructor
    · simpa [mem_closedBall, dist_eq_norm, haR.le] using haR.le
    · simp
  have hKne : K.Nonempty := ⟨(a : ℂ), haK⟩
  have huOn : ContinuousOn u K := by
    apply (regularVerticalAuxiliary_continuousOn_upperHalfPlane
      F hc hs0 hs1 ξ hξ).comp
        (by fun_prop : ContinuousOn (fun z : ℂ => (z.re, z.im)) K)
    intro z hz
    exact hz.2
  have hVOn : ContinuousOn V K := by
    exact (huOn.add ((by fun_prop : Continuous (fun z : ℂ => p * z.im)).continuousOn))
      |>.add ((by fun_prop : Continuous (fun z : ℂ => p * z.im^2)).continuousOn)
  obtain ⟨z, hzK, hzmax⟩ := hcompact.exists_isMaxOn hKne hVOn
  have hVbase : m ≤ V z := by
    have hbase : V (a : ℂ) = m := by simp [V, m]
    have hmaxbase : V (a : ℂ) ≤ V z := hzmax haK
    simpa only [hbase] using hmaxbase
  have hzR : ‖z‖ < R := by
    have hzle : ‖z‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hzK.1
    by_contra hn
    have heq : ‖z‖ = R := le_antisymm hzle (le_of_not_gt hn)
    have hzim : 0 ≤ z.im := hzK.2
    have himR : z.im ≤ R := by
      have h := Complex.abs_im_le_norm z
      rw [heq] at h
      exact le_trans (le_abs_self _) h
    have hfarArg : R₀ ≤ |z.re| + z.im := by
      have hnorm := Complex.norm_le_abs_re_add_abs_im z
      rw [heq, abs_of_nonneg hzim] at hnorm
      linarith
    have huBound : u z ≤ m / 4 := hfar z.re z.im hzim hfarArg
    have hpert : p * z.im + p * z.im^2 ≤ p * (R + R^2) := by
      have hsq : z.im^2 ≤ R^2 := by nlinarith
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr himR),
        mul_nonneg hp.le (sub_nonneg.mpr hsq)]
    have hVlt : V z < m := by
      dsimp [V]
      linarith
    exact not_lt_of_ge hVbase hVlt
  by_cases hzim : 0 < z.im
  · obtain ⟨r₀, hr₀, hsub⟩ :=
      regularVerticalAuxiliary_local_circle_submean
        F hc hs0 hs1 ξ hξ z.re z.im hzim
    let ρ : ℝ := min r₀ (min z.im (R - ‖z‖)) / 2
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρr : ρ < r₀ := by dsimp [ρ]; linarith [min_le_left r₀ (min z.im (R - ‖z‖))]
    have hρh : ρ < z.im := by
      dsimp [ρ]
      linarith [min_le_right r₀ (min z.im (R - ‖z‖)),
        min_le_left z.im (R - ‖z‖)]
    have hρR : ρ < R - ‖z‖ := by
      dsimp [ρ]
      linarith [min_le_right r₀ (min z.im (R - ‖z‖)),
        min_le_right z.im (R - ‖z‖)]
    have hsubz := hsub ρ hρ hρr
    have hzc : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
    have hstrict := regularVerticalAuxiliary_perturbed_strict_circle_submean
      F hc hs0 hs1 ξ hξ z.re z.im ρ p p hzim hρ hρh hp hsubz
    rw [hzc] at hstrict
    have hcircleSubset : sphere z ρ ⊆ K := by
      intro y hy
      have hyDist : ‖y - z‖ = ρ := by
        simpa only [mem_sphere, dist_eq_norm, abs_of_pos hρ] using hy
      constructor
      · have hyNorm : ‖y‖ ≤ ‖z‖ + ρ := by
          calc
            ‖y‖ = ‖(y-z)+z‖ := by congr 1; abel
            _ ≤ ‖y-z‖ + ‖z‖ := norm_add_le _ _
            _ = ‖z‖ + ρ := by rw [hyDist]; ring
        simpa only [mem_closedBall, dist_zero_right] using
          (le_of_lt (by linarith : ‖y‖ < R))
      · have him := Complex.abs_im_le_norm (y - z)
        rw [hyDist] at him
        have hdiff : (y-z).im = y.im-z.im := by simp
        rw [hdiff] at him
        have hlow := (abs_le.mp him).1
        change 0 ≤ y.im
        linarith [hρh]
    have hVci : CircleIntegrable V z ρ :=
      (hVOn.mono hcircleSubset).circleIntegrable hρ.le
    have hmeanle : Real.circleAverage V z ρ ≤ V z :=
      Real.circleAverage_mono_on_of_le_circle hVci
        (fun y hy => hzmax (hcircleSubset (by simpa only [abs_of_pos hρ] using hy)))
    have hstrictV : V z < Real.circleAverage V z ρ := by
      simpa only [V] using hstrict
    exact (not_lt_of_ge hmeanle hstrictV)
  · have hzim0 : z.im = 0 := le_antisymm (le_of_not_gt hzim) hzK.2
    have hpos : 0 < ∫ t : ℝ,
        regularExteriorVerticalPotentialDifference F s ξ z.re t := by
      have hzReal : (z.re : ℂ) = z := by
        conv_rhs => rw [← Complex.re_add_im z]
        simp [hzim0]
      have hVm : m ≤ u z := by
        dsimp [V] at hVbase
        rw [hzim0] at hVbase
        simpa using hVbase
      rw [← hboundary, hzReal]
      exact lt_of_lt_of_le hm hVm
    obtain ⟨δ, hδ, hslope⟩ :=
      regularVerticalAuxiliary_boundary_slope_le
        F hc hs0 hs1 ξ hξ z.re hpos (p/2) (by positivity)
    let t : ℝ := min δ (R - ‖z‖) / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ (R - ‖z‖)]
    have htR : t < R - ‖z‖ := by
      dsimp [t]
      linarith [min_le_right δ (R - ‖z‖)]
    let y : ℂ := z + (t : ℂ) * Complex.I
    have hyK : y ∈ K := by
      constructor
      · have hnorm : ‖y‖ ≤ ‖z‖ + t := by
          calc
            ‖y‖ ≤ ‖z‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
            _ = ‖z‖ + t := by simp [abs_of_pos ht]
        simpa only [mem_closedBall, dist_zero_right] using
          (le_of_lt (by linarith : ‖y‖ < R))
      · simp [y, hzim0, ht.le]
    have hyre : y.re = z.re := by simp [y]
    have hyim : y.im = t := by simp [y, hzim0]
    have hsl := hslope t ht htδ
    have hVinc : V z < V y := by
      dsimp [V, u]
      rw [hzim0, hyre, hyim]
      have hposTerm : 0 ≤ p*t^2 := by positivity
      nlinarith
    exact not_lt_of_ge (hzmax hyK) hVinc

end SpringerLean