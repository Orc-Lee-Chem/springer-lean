import SpringerLean.Round1560AnnulusToDiskGain

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The cubic gain holds for the actual harmonic filling on a complete
compact disk of some radius below one. -/
theorem actualHarmonic_positivePower_exists_interiorDisk_cubic_gain
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {h d : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {m : ℕ} (hm : 1500 ≤ m) (hD : (m:ℝ)*d ≤ 3/20) :
    let D := (m:ℝ)*d
    let a := 1-Real.sqrt d/16
    ∃ b : ℝ, a ≤ b ∧ b < 1 ∧
      D^3/30 <
        ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
        (∫ z in greenPolarRegion 0 b,
          (max (2*z.re) 0)^m-
            (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
  dsimp only
  let a : ℝ := 1-Real.sqrt d/16
  have ha1 : a ≤ 1 := by
    dsimp [a]
    linarith [Real.sqrt_nonneg d]
  have hpb := thinAnnulus_peak_parameter_bounds hm hd0 hD
    (show 1-Real.sqrt d/16 ≤ a by rfl) ha1
  have ha0 : 0 ≤ a := by
    have ha99 : (99/100:ℝ) ≤ a := by simpa only [a] using hpb.2.2
    linarith
  obtain ⟨b,hab,hb1,hgain⟩ :=
    actualHarmonic_positivePower_exists_annulus_cubic_gain
      F hc ξ hξ hh0 hhpi hd hd0 hcap hm hD
  refine ⟨b,hab,hb1,?_⟩
  exact actualHarmonic_positivePower_annulus_to_disk_gain
    F hc ξ hξ ha0 hab hb1 (by omega : 1 ≤ m) hgain

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_exists_interiorDisk_cubic_gain
