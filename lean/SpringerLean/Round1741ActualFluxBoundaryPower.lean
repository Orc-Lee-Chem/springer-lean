import SpringerLean.Round1740ActualEnergyIntegrationReduction

open scoped ComplexConjugate

namespace SpringerLean

theorem energyMultipliers_common_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |energyMultiplierChi t| ≤ C ∧
      |energyMultiplierF t| ≤ C ∧
      |energyMultiplierSigma t| ≤ C := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := energyMultipliers_bounded
  refine ⟨|a| + |b| + |c|, by positivity, ?_⟩
  intro t ht
  have h₁ := (ha t ht).trans (le_abs_self a)
  have h₂ := (hb t ht).trans (le_abs_self b)
  have h₃ := (hc t ht).trans (le_abs_self c)
  constructor
  · linarith [abs_nonneg b, abs_nonneg c]
  constructor <;> linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]

theorem energyMultipliers_common_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |energyMultiplierChi t| ≤ C * t ∧
      |energyMultiplierF t| ≤ C * t ∧
      |energyMultiplierSigma t| ≤ C * t := by
  have hchi : ∃ a : NNReal, LipschitzWith a energyMultiplierChi :=
    ⟨_, energyMultiplierChi_lipschitz⟩
  have hf : ∃ a : NNReal, LipschitzWith a energyMultiplierF :=
    ⟨_, energyMultiplierF_lipschitz⟩
  have hs : ∃ a : NNReal, LipschitzWith a energyMultiplierSigma :=
    ⟨_, energyMultiplierSigma_lipschitz⟩
  obtain ⟨a, ha⟩ := hchi
  obtain ⟨b, hb⟩ := hf
  obtain ⟨c, hc⟩ := hs
  refine ⟨(a : ℝ) + b + c, by positivity, ?_⟩
  intro t ht
  have h₁ := lipschitz_zero_linear_bound _ ha energyMultipliers_zero.1 t
  have h₂ := lipschitz_zero_linear_bound _ hb energyMultipliers_zero.2.1 t
  have h₃ := lipschitz_zero_linear_bound _ hc energyMultipliers_zero.2.2 t
  rw [abs_of_nonneg ht] at h₁ h₂ h₃
  have hat : 0 ≤ (a : ℝ)*t := mul_nonneg a.coe_nonneg ht
  have hbt : 0 ≤ (b : ℝ)*t := mul_nonneg b.coe_nonneg ht
  have hct : 0 ≤ (c : ℝ)*t := mul_nonneg c.coe_nonneg ht
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- A common multiplier bound gives a bound for the actual signed
flux, with the analytic derivative appearing only linearly. -/
theorem actualEnergyFluxField_norm_le_common_multiplier
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hH : actualHarmonic F z ≠ 0)
    (L : ℝ) (hL : 0 ≤ L)
    (hchi : |energyMultiplierChi (actualHarmonicMultiplierTime F k z)| ≤ L)
    (hf : |energyMultiplierF (actualHarmonicMultiplierTime F k z)| ≤ L)
    (hs : |energyMultiplierSigma (actualHarmonicMultiplierTime F k z)| ≤ L) :
    ‖actualEnergyFluxField F k beta z‖ ≤
      (14 * (k : ℝ) * L) * ‖actualHarmonic F z‖^(2*k-1) *
        (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  let c := ‖deriv (exteriorForwardGerm F) (conj z)‖
  have hc0 : 0 ≤ c := norm_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨hx, hy⟩ := actualHarmonicPhase_gradient_coordinates_abs_le
    F hc k beta hbeta hz
  have hx' : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)| ≤
      ((k : ℝ) * (1+c)) * ‖actualHarmonic F z‖^(k-1) := by
    nlinarith [hx]
  have hy' : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I| ≤
      ((k : ℝ) * (1+c)) * ‖actualHarmonic F z‖^(k-1) := by
    nlinarith [hy]
  have hraw := actualEnergyFluxField_norm_le_power F k hk beta z hbeta hH
    L L L ((k : ℝ)*(1+c)) hchi hf hs hx' hy'
  have hcoeff :
      2*L*((k : ℝ)*(1+c)) + 8*((k : ℝ)-1)*L +
        4*((k : ℝ)-1)*L ≤ (14*(k : ℝ)*L)*(1+c) := by
    nlinarith [mul_nonneg hL hc0, mul_nonneg hk0 (mul_nonneg hL hc0)]
  calc
    _ ≤ _ := hraw
    _ ≤ ((14*(k : ℝ)*L)*(1+c))*‖actualHarmonic F z‖^(2*k-1) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring

/-- Inner and outer boundary power bounds for the same actual flux.
The constants are uniform over the whole source disk. -/
theorem actualEnergyFluxField_boundary_power_bounds
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ < 1 →
      ‖actualEnergyFluxField F k beta z‖ ≤
        C * ‖actualHarmonic F z‖^(2*k-1) *
          (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) ∧
      ‖actualEnergyFluxField F k beta z‖ ≤
        C * (1-‖z‖) * ‖actualHarmonic F z‖^(2*k-2) *
          (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  obtain ⟨B, hB, hbound⟩ := energyMultipliers_common_bounded
  obtain ⟨L, hL, hlinear⟩ := energyMultipliers_common_linear_bound
  let C₀ := 14 * (k : ℝ) * B
  let C₁ := 14 * (k : ℝ)^2 * L
  refine ⟨C₀+C₁, by dsimp [C₀, C₁]; positivity, ?_⟩
  intro z hz
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hr : 0 ≤ 1-‖z‖ := sub_nonneg.mpr hz.le
  by_cases hH : actualHarmonic F z = 0
  · have hJ := (actualEnergyFluxFields_zero_at_filling_zero
      F hc k hk beta hz hH).2.2.2
    rw [hJ, norm_zero]
    constructor <;> positivity
  · let y := ‖actualHarmonic F z‖
    let t := actualHarmonicMultiplierTime F k z
    have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
    have hBz := hbound t ht
    have hLz := hlinear t ht
    have hinner := actualEnergyFluxField_norm_le_common_multiplier
      F hc k hk beta hbeta hz hH B hB hBz.1 hBz.2.1 hBz.2.2
    have houter := actualEnergyFluxField_norm_le_common_multiplier
      F hc k hk beta hbeta hz hH (L*t) (mul_nonneg hL ht)
      hLz.1 hLz.2.1 hLz.2.2
    have hpow : t * y^(2*k-1) =
        (k : ℝ)*(1-‖z‖)*y^(2*k-2) := by
      have hy : y ≠ 0 := norm_ne_zero_iff.mpr hH
      have hn : 2*k-1 = (2*k-2)+1 := by omega
      dsimp [t, actualHarmonicMultiplierTime]
      change (k : ℝ)*(1-‖z‖)/y*y^(2*k-1) = _
      rw [hn, pow_succ]
      field_simp
    constructor
    · calc
        _ ≤ _ := hinner
        _ ≤ _ := by dsimp [C₀]; gcongr; linarith
    · have houter' : ‖actualEnergyFluxField F k beta z‖ ≤
          C₁ * (1-‖z‖) * y^(2*k-2) *
            (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
        calc
          _ ≤ _ := houter
          _ = (14*(k : ℝ)*L) * (t*y^(2*k-1)) *
              (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by ring
          _ = _ := by rw [hpow]; dsimp [C₁]; ring
      calc
        _ ≤ _ := houter'
        _ ≤ _ := by gcongr; linarith

/-- Both collars are controlled by the same distance-to-boundary
factor and the same integrable analytic-derivative majorant. -/
theorem actualEnergyFluxField_norm_le_boundary_distance
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ < 1 →
      ‖actualEnergyFluxField F k beta z‖ ≤
        C * min ‖z‖ (1-‖z‖) *
          (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    actualEnergyFluxField_boundary_power_bounds F hc k hk beta hbeta
  let K := C*((2 : ℝ)^(2*k-1)+(2 : ℝ)^(2*k-2))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro z hz
  have hr : 0 ≤ ‖z‖ := norm_nonneg _
  have ho : 0 ≤ 1-‖z‖ := by linarith
  have hH := actualHarmonic_norm_le_two_norm F hc hz
  have hHtwo : ‖actualHarmonic F z‖ ≤ 2 := by linarith
  have hpower : ‖actualHarmonic F z‖^(2*k-1) ≤
      (2 : ℝ)^(2*k-1)*‖z‖ := by
    have hrpow : ‖z‖^(2*k-1) ≤ ‖z‖ := by
      have hn : 2*k-1 = (2*k-2)+1 := by omega
      rw [hn, pow_succ]
      exact (mul_le_mul_of_nonneg_right
        (pow_le_one₀ hr hz.le) hr).trans_eq (one_mul _)
    calc
      _ ≤ (2*‖z‖)^(2*k-1) := pow_le_pow_left₀ (norm_nonneg _) hH _
      _ = (2 : ℝ)^(2*k-1)*‖z‖^(2*k-1) := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hrpow (by positivity)
  have hpower' := pow_le_pow_left₀ (norm_nonneg _) hHtwo (2*k-2)
  obtain ⟨hi, hout⟩ := hbound z hz
  have hCi : C*(2 : ℝ)^(2*k-1) ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2*k-2))]
  have hCo : C*(2 : ℝ)^(2*k-2) ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2*k-1))]
  have hi' : ‖actualEnergyFluxField F k beta z‖ ≤
      K*‖z‖*(1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by
    calc
      _ ≤ _ := hi
      _ ≤ C*((2 : ℝ)^(2*k-1)*‖z‖)*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by gcongr
      _ = (C*(2 : ℝ)^(2*k-1))*‖z‖*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by ring
      _ ≤ _ := by gcongr
  have ho' : ‖actualEnergyFluxField F k beta z‖ ≤
      K*(1-‖z‖)*(1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by
    calc
      _ ≤ _ := hout
      _ ≤ C*(1-‖z‖)*(2 : ℝ)^(2*k-2)*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by gcongr
      _ = (C*(2 : ℝ)^(2*k-2))*(1-‖z‖)*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by ring
      _ ≤ _ := by gcongr
  rcases le_total ‖z‖ (1-‖z‖) with h | h
  · simpa only [min_eq_left h] using hi'
  · simpa only [min_eq_right h] using ho'

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_norm_le_common_multiplier
#print axioms SpringerLean.actualEnergyFluxField_boundary_power_bounds
#print axioms SpringerLean.actualEnergyFluxField_norm_le_boundary_distance
