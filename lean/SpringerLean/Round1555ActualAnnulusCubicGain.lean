import SpringerLean.Round1554TruncatedAnnulusMargin

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- A genuine cubic saving for the actual harmonic filling on one closed
annulus strictly inside the disk. The area measure is divided by pi, and
the coefficient normalization is `m sqrt(m)/2^m`. -/
theorem actualHarmonic_positivePower_exists_annulus_cubic_gain
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
        (∫ z in greenPolarRegion a b,
          (max (2*z.re) 0)^m-
            (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
  dsimp only
  let D : ℝ := (m:ℝ)*d
  let a : ℝ := 1-Real.sqrt d/16
  let K : ℝ := (9/(50*Real.pi):ℝ)*(m:ℝ)*((m:ℝ)-1)*d^2*Real.sqrt d
  obtain ⟨b, hab, hb1, hmargin⟩ :=
    thinAnnulus_exists_truncated_cubic_margin hm hd0 hD
  change D^3/30 <
    (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*(b^m-a^m)
    at hmargin
  have hactual := actualHarmonic_positivePower_thinAnnulus_integral_gain
    F hc ξ hξ hh0 hhpi hd hd0 hcap hm hD hab hb1
  change K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ)) ≤
    Real.pi⁻¹*(∫ z in greenPolarRegion a b,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m) at hactual
  have hnorm := thinAnnulus_normalization_identity hm hd0
    (u := b^m-a^m)
  change ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*
      (K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ))) =
    (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*(b^m-a^m)
    at hnorm
  have hmult : 0 ≤ (m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m := by positivity
  refine ⟨b, hab, hb1, ?_⟩
  calc
    D^3/30 < (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*
        (b^m-a^m) := hmargin
    _ = ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*
          (K*2^(m-1:ℕ)*((b^m-a^m)/(m:ℝ))) := hnorm.symm
    _ ≤ ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
          (∫ z in greenPolarRegion a b,
            (max (2*z.re) 0)^m-
              (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
      convert mul_le_mul_of_nonneg_left hactual hmult using 1 <;> ring

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_exists_annulus_cubic_gain
