import SpringerLean.SingleRampFlux
import SpringerLean.Round1720FluxZeroPowerCriterion
import SpringerLean.Round1721ActualFillingLocalLinearZero
import SpringerLean.Round1722ActualPhaseGradientPowerBound
import SpringerLean.Round1723ActualGermDerivativeLocallyBounded
import SpringerLean.Round1725PhasePowerDivision

open Filter MeasureTheory Metric
open scoped Topology ComplexConjugate

namespace SpringerLean.AnalyticRevision

noncomputable section

/-- At a filling zero both parts of the flux vanish under real division. -/
theorem rampFlux_eq_zero (F : ℂ → ℂ) (k : ℕ) (β z : ℂ)
    (hk : 2 ≤ k) (hH : actualHarmonic F z = 0) :
    rampFlux F k β z = 0 := by
  have hU : actualHarmonicPhaseField F k β z = 0 := by
    simp [actualHarmonicPhaseField, hH, zero_pow (by omega : k ≠ 0)]
  apply Complex.ext <;> simp [rampFlux, rampFluxP, rampFluxR, hU, Complex.smul_re, Complex.smul_im]

private def rampFluxAmplitude (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k β
  let A := (U z)^2/‖actualHarmonic F z‖
  U z • Complex.mk (fderiv ℝ U z (1:ℂ)) (fderiv ℝ U z Complex.I) +
    (4*((k:ℝ)-1)/6*A) • (‖z‖⁻¹ • z)

private theorem rampFlux_eq_smul (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) :
    rampFlux F k β z =
      ramp (actualHarmonicMultiplierTime F k z) • rampFluxAmplitude F k β z := by
  apply Complex.ext <;>
    simp only [rampFlux, rampFluxP, rampFluxR, rampFluxAmplitude,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, div_eq_mul_inv] <;> ring

private theorem rampFluxAmplitude_norm_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖rampFluxAmplitude F k β z‖ ≤
      3*(k:ℝ)*‖actualHarmonic F z‖^(2*k-1)*
        (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  let U := actualHarmonicPhaseField F k β
  let y := ‖actualHarmonic F z‖
  let ux := fderiv ℝ U z (1:ℂ)
  let uy := fderiv ℝ U z Complex.I
  let c := ‖deriv (exteriorForwardGerm F) (conj z)‖
  let A := (U z)^2/y
  let b := 4*((k:ℝ)-1)/6
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hA₀ : 0 ≤ A := by dsimp [A,y]; positivity
  have hA : A ≤ y^(2*k-1) := by
    by_cases hy : y = 0
    · simp [A,hy]
    · exact phase_square_div_le_power y (U z) k (by omega)
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy))
        (actualHarmonicPhaseField_abs_le_power F k β z hβ)
  obtain ⟨hux,huy⟩ := actualHarmonicPhase_gradient_coordinates_abs_le F hc k β hβ hz
  have hU := actualHarmonicPhaseField_abs_le_power F k β z hβ
  have hgrad : ‖Complex.mk ux uy‖ ≤ 2*((k:ℝ)*y^(k-1)*(1+c)) := by
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.mk ux uy)
    change ‖Complex.mk ux uy‖ ≤ |ux| + |uy| at h
    change |ux| ≤ _ at hux
    change |uy| ≤ _ at huy
    change |ux| ≤ (k:ℝ)*y^(k-1)*(1+c) at hux
    change |uy| ≤ (k:ℝ)*y^(k-1)*(1+c) at huy
    linarith only [h,hux,huy]
  have hr : ‖‖z‖⁻¹ • z‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_inv_mul]
    exact div_self_le_one _
  have hb' : b ≤ (k:ℝ)*(1+c) := by
    dsimp [b]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (show 0 ≤ c from norm_nonneg _)]
  have hpow : y^k*y^(k-1) = y^(2*k-1) := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ ‖U z • Complex.mk ux uy‖ + ‖(b*A) • (‖z‖⁻¹ • z)‖ := norm_add_le _ _
    _ = |U z| * ‖Complex.mk ux uy‖ + b*A*‖‖z‖⁻¹ • z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hb hA₀)]
    _ ≤ y^k * (2*((k:ℝ)*y^(k-1)*(1+c))) + (k:ℝ)*(1+c)*y^(2*k-1)*1 := by
      change |U z| ≤ y^k at hU
      gcongr
    _ = _ := by linear_combination (2*(k:ℝ)*(1+c)) * hpow

/-- The uniform bound and the boundary-vanishing bound for the same
flux, with the analytic derivative appearing to the first power. -/
theorem rampFlux_power_bounds
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    let y := ‖actualHarmonic F z‖
    let c := ‖deriv (exteriorForwardGerm F) (conj z)‖
    ‖rampFlux F k β z‖ ≤ (9/5)*(3*(k:ℝ))*y^(2*k-1)*(1+c) ∧
    ‖rampFlux F k β z‖ ≤ 36*(k:ℝ)^2*(1-‖z‖)*y^(2*k-2)*(1+c) := by
  let y := ‖actualHarmonic F z‖
  let c := ‖deriv (exteriorForwardGerm F) (conj z)‖
  let t := actualHarmonicMultiplierTime F k z
  have ⟨hχ₀, hχ₁, hχ₂⟩ := ramp_bounds (actualHarmonicMultiplierTime_nonneg F k hz)
  have ha := rampFluxAmplitude_norm_le F hc k hk β hβ hz
  have hbase : ‖rampFlux F k β z‖ ≤ ramp t*(3*(k:ℝ)*y^(2*k-1)*(1+c)) := by
    rw [rampFlux_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hχ₀]
    exact mul_le_mul_of_nonneg_left ha hχ₀
  dsimp only
  constructor
  · exact (hbase.trans (mul_le_mul_of_nonneg_right hχ₁ (by dsimp [y,c]; positivity))).trans_eq (by ring)
  · by_cases hH : actualHarmonic F z = 0
    · rw [rampFlux_eq_zero F k β z hk hH, norm_zero]
      have : 0 ≤ 1-‖z‖ := by linarith
      positivity
    · have hpow : t*y^(2*k-1) = (k:ℝ)*(1-‖z‖)*y^(2*k-2) := by
        have hy : y ≠ 0 := norm_ne_zero_iff.mpr hH
        have hn : 2*k-1 = (2*k-2)+1 := by omega
        change (k:ℝ)*(1-‖z‖)/y*y^(2*k-1) = _
        rw [hn, pow_succ]
        field_simp
      calc
        _ ≤ (12*t)*(3*(k:ℝ)*y^(2*k-1)*(1+c)) :=
          hbase.trans (mul_le_mul_of_nonneg_right hχ₂ (by dsimp [y,c]; positivity))
        _ = _ := by linear_combination (36*(k:ℝ)*(1+c)) * hpow

theorem rampFlux_norm_le_boundary_distance
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ < 1 →
      ‖rampFlux F k β z‖ ≤
        C * min ‖z‖ (1-‖z‖) * (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by
  let C₁ := (9/5)*(3*(k:ℝ))*(2:ℝ)^(2*k-1)
  let C₂ := 36*(k:ℝ)^2*(2:ℝ)^(2*k-2)
  have h₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have h₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  refine ⟨C₁+C₂, add_nonneg h₁ h₂, ?_⟩
  intro z hz
  have hr : 0 ≤ ‖z‖ := norm_nonneg _
  have ho : 0 ≤ 1-‖z‖ := by linarith
  have hH := actualHarmonic_norm_le_two_norm F hc hz
  have hy : ‖actualHarmonic F z‖ ≤ 2 := by linarith
  have hn : 2*k-1 = (2*k-2)+1 := by omega
  have hp : ‖actualHarmonic F z‖^(2*k-1) ≤
      (2:ℝ)^(2*k-1)*‖z‖ := by
    calc
      _ ≤ (2*‖z‖)^(2*k-1) := pow_le_pow_left₀ (norm_nonneg _) hH _
      _ = (2:ℝ)^(2*k-1)*‖z‖^(2*k-1) := mul_pow _ _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hn, pow_succ]
        exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hr hz.le) hr).trans_eq (one_mul _)
  obtain ⟨hi,he⟩ := rampFlux_power_bounds F hc k hk β hβ hz
  rcases le_total ‖z‖ (1-‖z‖) with h | h
  · rw [min_eq_left h]
    apply hi.trans
    calc
      _ ≤ (9/5)*(3*(k:ℝ))*((2:ℝ)^(2*k-1)*‖z‖)*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by gcongr
      _ = C₁*‖z‖*(1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by dsimp [C₁]; ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right h₂
  · rw [min_eq_right h]
    apply he.trans
    calc
      _ ≤ 36*(k:ℝ)^2*(1-‖z‖)*(2:ℝ)^(2*k-2)*
          (1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by gcongr
      _ = C₂*(1-‖z‖)*(1+‖deriv (exteriorForwardGerm F) (conj z)‖) := by dsimp [C₂]; ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left h₁

theorem rampFlux_hasFDerivAt_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hzero : actualHarmonic F z = 0) :
    HasFDerivAt (rampFlux F k β) (0 : ℂ →L[ℝ] ℂ) z := by
  let n := 2*k-1
  obtain ⟨L,hL,hlinear⟩ := actualHarmonic_local_linear_at_zero F hc hz hzero
  obtain ⟨B,hB,hgerm⟩ := actualHarmonic_germ_deriv_locally_bounded F hc hz
  apply hasFDerivAt_zero_of_power_bound _ _ n (by dsimp [n]; omega)
    (rampFlux_eq_zero F k β z hk hzero) ((9/5)*(3*(k:ℝ))*L^n*(1+B))
  have hz' : z ∈ ball (0:ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hz
  filter_upwards [hlinear,hgerm,isOpen_ball.mem_nhds hz'] with w hw hg hb
  have hb' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hb
  have hp := pow_le_pow_left₀ (norm_nonneg _) hw n
  calc
    _ ≤ _ := (rampFlux_power_bounds F hc k hk β hβ hb').1
    _ ≤ (9/5)*(3*(k:ℝ))*(L*‖w-z‖)^n*(1+B) := by gcongr
    _ = _ := by rw [mul_pow]; ring

private theorem locally_smul (a : ℂ → ℝ) (J : ℂ → ℂ) (z : ℂ)
    (ha : ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K a s)
    (hJ : ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K J s) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K (fun w => a w • J w) s := by
  have h : ContDiffAt ℝ 1 (fun p : ℝ × ℂ => p.1 • p.2) (a z, J z) := by fun_prop
  exact local_lipschitz_comp _ _ z
    (local_lipschitz_prodMk a J z ha hJ) h.exists_lipschitzOnWith

theorem rampFlux_locally_lipschitz_punctured_disk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz₀ : z ≠ 0) :
    ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K (rampFlux F k β) s := by
  let U := actualHarmonicPhaseField F k β
  let A : ℂ → ℝ := fun w => (U w)^2/‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  let c : ℝ := 4*((k:ℝ)-1)/6
  let L (J : ℂ → ℂ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K J s
  let Lr (a : ℂ → ℝ) := ∃ K : NNReal, ∃ s ∈ 𝓝 z, LipschitzOnWith K a s
  have hU : Lr U :=
    (actualHarmonicPhaseField_contDiffAt_real F hc k β hz).exists_lipschitzOnWith
  obtain ⟨hx,hy⟩ := actualHarmonicPhase_gradient_coordinates_contDiffAt F hc k β hz
  have hP : L (fun w => U w • Complex.mk (fderiv ℝ U w (1:ℂ))
      (fderiv ℝ U w Complex.I)) :=
    locally_smul _ _ z hU (local_lipschitz_complex_mk _ _ z
      hx.exists_lipschitzOnWith hy.exists_lipschitzOnWith)
  obtain ⟨s,hs,⟨KA,hA⟩,_⟩ :=
    actualEnergyFlux_quotient_amplitudes_locally_lipschitz F hc k (by omega) β hβ hz
  have hconst (b : ℝ) : Lr (fun _ => b) :=
    (show ContDiffAt ℝ 1 (fun _ : ℂ => b) z from contDiffAt_const).exists_lipschitzOnWith
  have hdir : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖⁻¹ • w) z := by
    have hr : ContDiffAt ℝ 1 (fun w : ℂ => ‖w‖) z := contDiffAt_id.norm (𝕜 := ℂ) hz₀
    exact (hr.inv (norm_ne_zero_iff.mpr hz₀)).smul contDiffAt_id
  have hR : L (fun w => (c*A w) • (‖w‖⁻¹ • w)) :=
    locally_smul _ _ z (local_lipschitz_mul _ _ z (hconst c) ⟨KA,s,hs,hA⟩)
      hdir.exists_lipschitzOnWith
  have hamp : L (rampFluxAmplitude F k β) :=
    local_lipschitz_add _ _ z hP hR
  by_cases hzero : actualHarmonic F z = 0
  · have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    let q : ℂ → ℝ := fun w => (k:ℝ)*(1-‖w‖) - (3/20)*‖actualHarmonic F w‖
    have hq : 0 < q z := by
      simpa only [q,hzero,norm_zero,mul_zero,sub_zero] using
        mul_pos hkpos (sub_pos.mpr hz)
    have hqc : ContinuousAt q z :=
      (continuousAt_const.mul (continuousAt_const.sub continuous_norm.continuousAt)).sub
        (continuousAt_const.mul (actualHarmonic_contDiffAt_real F hc hz).continuousAt.norm)
    apply local_lipschitz_of_eventuallyEq (rampFlux F k β)
      (fun w => (9/5:ℝ) • rampFluxAmplitude F k β w) z
    · filter_upwards [hqc.eventually (lt_mem_nhds hq)] with w hw
      by_cases hH : actualHarmonic F w = 0
      · have hUw : U w = 0 := by
          simp [U,actualHarmonicPhaseField,hH,zero_pow (by omega : k ≠ 0)]
        have h' : actualHarmonicPhaseField F k β w = 0 := hUw
        simp [rampFlux_eq_zero F k β w hk hH,rampFluxAmplitude,h']
      · have ht : (3/20:ℝ) < t w := by
          change 3/20 < (k:ℝ)*(1-‖w‖)/‖actualHarmonic F w‖
          exact (lt_div_iff₀ (norm_pos_iff.mpr hH)).mpr (sub_pos.mp hw)
        rw [rampFlux_eq_smul, show actualHarmonicMultiplierTime F k w = t w from rfl]
        rw [show ramp (t w) = 9/5 from min_eq_right (by linarith)]
    · exact locally_smul _ _ z (hconst _) hamp
  · obtain ⟨K,s,hs,ht⟩ := actualHarmonicMultiplierTime_locally_lipschitz_regular
      F hc k hz hz₀ hzero
    have hχ : Lr (fun w => ramp (t w)) :=
      ⟨_,s,hs,ramp_lipschitz.comp_lipschitzOnWith ht⟩
    have h := locally_smul _ _ z hχ hamp
    have heq : rampFlux F k β = (fun w => ramp (t w) • rampFluxAmplitude F k β w) :=
      funext (rampFlux_eq_smul F k β)
    rwa [heq]

theorem rampFlux_continuousOn_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1) :
    ContinuousOn (rampFlux F k β) (ball (0:ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  by_cases hz₀ : z = 0
  · subst z
    have hH : actualHarmonic F 0 = 0 := by simp [actualHarmonic, exteriorForwardGerm_zero]
    exact (rampFlux_hasFDerivAt_zero F hc k hk β hβ hz' hH).continuousAt.continuousWithinAt
  · obtain ⟨K,s,hs,hJ⟩ := rampFlux_locally_lipschitz_punctured_disk F hc k hk β hβ hz' hz₀
    exact (hJ.continuousOn.continuousAt hs).continuousWithinAt

end
end SpringerLean.AnalyticRevision
