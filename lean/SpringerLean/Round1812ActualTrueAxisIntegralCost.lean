import SpringerLean.Round1809TrueAxisReferenceMoment
import SpringerLean.Round1811ActualEndpointPhaseIntegral

open MeasureTheory Metric Set
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 800000

/-- A true-axis lower power has the exact uncut reference cost used by
the other phase branch; no directional moment premise is left. -/
theorem actualHarmonic_trueAxis_integral_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (ξ : ℂ) (hξ : ‖ξ‖=1) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
      trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*
        (max ((conj ξ*actualHarmonic F z).re/2) 0)^(2*k-10)) ≤
      (1-1/((2*k-2 : ℕ) : ℝ))*comparisonPositiveDiskMoment (2*k-2) := by
  let j := 2*k-10
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hconv : ConvexOn ℝ univ (fun x : ℝ => (max (x/2) 0)^j) := by
    have hh := positivePart_pow_convexOn j hj
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simpa only [smul_eq_mul,add_div,mul_div_assoc] using
      hh.2 (mem_univ (x/2)) (mem_univ (y/2)) ha hb hab
  have hle := actualHarmonic_disk_convex_le F hc ξ hξ _ hconv
  have hm : (1500 : ℝ) ≤ ((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hh := mul_le_mul_of_nonneg_left hle (trueAxisMomentRatioLambda_pos_and_log hm).1.le
  simp only [show ∀ x : ℝ, 2*x/2=x from fun x => by ring] at hh
  rw [integral_const_mul]
  have hcost := trueAxisMomentRatioLambda_reference k hk
  dsimp [comparisonPositiveDiskMoment] at hcost ⊢
  dsimp [j] at hh
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.actualHarmonic_trueAxis_integral_le
