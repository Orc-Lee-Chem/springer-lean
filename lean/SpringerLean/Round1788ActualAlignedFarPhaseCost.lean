import SpringerLean.Round1787FarComplexPower
import SpringerLean.Round1785ActualAlignedNearPhaseCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 900000

/-- In the far aligned subregion the lower power controls even the
unsigned actual moment density. This branch needs no phase saving. -/
theorem actualSignedPhaseDensity_aligned_far_lt_lower_power
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (ha : 6 ≤ a)
    (hs : 7*a/5 ≤ ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2)) :
    actualSignedPhaseDensity F k beta z <
      (2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*
        (max ((conj v*actualHarmonic F z).re) 0)^(2*k-10)/(2 : ℝ)^(2*k-2) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let w := actualHarmonic F z
  let x := (conj v*w).re
  let s := m*(1-x/2)
  have hx0 : 0 < x := by dsimp [x, w]; linarith
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < 2*k-2)
  obtain ⟨hy0, hy1, hQ0, hs0, hH0, hquad, hslope⟩ :=
    exteriorOmitted_actualEndpoint_aligned_scaled_strip F hc k hk P hP hd ht hW v δ hv hδ
      w (actualHarmonic_mem_convexHull_omitted F hc hz) hx
  have hfar := aligned_strip_far_cost hy0 hy1 hQ0 hs0 ha hs hH0 hslope hquad
  have has : a ≤ s := by change 7*a/5 ≤ s at hs; linarith
  have hsm : s < m := by
    dsimp [s]
    nlinarith [mul_pos hm0 hx0]
  have hmn : m=2*((k-1 : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast (by omega : 2*k-2=2*(k-1))
  have hxs : x=2*(1-s/(2*((k-1 : ℕ) : ℝ))) := by
    rw [←hmn]
    dsimp [s]
    field_simp
    <;> ring
  have hcost : (2*((k-1 : ℕ) : ℝ))^2*(|(conj v*w).im|/x)^2/2 < 8*(s-a) := by
    rw [←hmn]
    change (m*|(conj v*w).im|/x)^2/2 < 8*(s-a) at hfar
    convert hfar using 1 <;> ring
  have hp := far_complex_power_le_lower_test (k-1) (by omega : 4 ≤ k-1) v w hvunit
    (by linarith : 0 ≤ a) has (by rw [←hmn]; exact hsm) hx0 hxs hcost
  have hexp : 2*(k-1)=2*k-2 := by omega
  have hexp' : 2*k-2-8=2*k-10 := by omega
  rw [hexp, hexp', ←hmn] at hp
  have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
    unfold actualHarmonicPhasePotentialDensity
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hraw : ‖w‖^(2*k-2)-(8/25 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤
      ‖w‖^(2*k-2) := by nlinarith
  unfold actualSignedPhaseDensity
  rw [max_eq_left hx0.le]
  exact (div_le_div_of_nonneg_right hraw (by positivity)).trans_lt
    (div_lt_div_of_pos_right hp (by positivity))

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_aligned_far_lt_lower_power
