import SpringerLean.Round1740ActualEnergyIntegrationReduction

open Filter Metric
open scoped Topology

namespace SpringerLean
noncomputable section

/-- A unit ramp, used at the two edges of a compact source annulus. -/
def energyUnitRamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem energyUnitRamp_bounds (x : ℝ) :
    0 ≤ energyUnitRamp x ∧ energyUnitRamp x ≤ 1 := by
  dsimp [energyUnitRamp]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem energyUnitRamp_eq_zero {x : ℝ} (hx : x ≤ 0) :
    energyUnitRamp x = 0 := by
  dsimp [energyUnitRamp]
  exact max_eq_left ((min_le_right _ _).trans hx)

theorem energyUnitRamp_eq_one {x : ℝ} (hx : 1 ≤ x) :
    energyUnitRamp x = 1 := by
  simp [energyUnitRamp, min_eq_left hx]

/-- The cutoff is zero on both boundary collars and one between the
two slightly larger collars. No boundary regularity of F is used. -/
def radialEnergyCutoff (ε : ℝ) (z : ℂ) : ℝ :=
  energyUnitRamp ((‖z‖-ε)/ε) *
    energyUnitRamp ((1-ε-‖z‖)/ε)

theorem radialEnergyCutoff_bounds (ε : ℝ) (z : ℂ) :
    0 ≤ radialEnergyCutoff ε z ∧ radialEnergyCutoff ε z ≤ 1 := by
  obtain ⟨ha, ha'⟩ := energyUnitRamp_bounds ((‖z‖-ε)/ε)
  obtain ⟨hb, hb'⟩ := energyUnitRamp_bounds ((1-ε-‖z‖)/ε)
  exact ⟨mul_nonneg ha hb,
    (mul_le_mul ha' hb' hb (by norm_num)).trans_eq (by norm_num)⟩

theorem radialEnergyCutoff_eq_zero_inner {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ ε) : radialEnergyCutoff ε z = 0 := by
  have h : (‖z‖-ε)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hz) hε.le
  simp [radialEnergyCutoff, energyUnitRamp_eq_zero h]

theorem radialEnergyCutoff_eq_zero_outer {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : 1-ε ≤ ‖z‖) : radialEnergyCutoff ε z = 0 := by
  have h : (1-ε-‖z‖)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hz) hε.le
  simp [radialEnergyCutoff, energyUnitRamp_eq_zero h]

theorem radialEnergyCutoff_eq_one {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hi : 2*ε ≤ ‖z‖) (ho : ‖z‖ ≤ 1-2*ε) :
    radialEnergyCutoff ε z = 1 := by
  have hi' : 1 ≤ (‖z‖-ε)/ε := (le_div_iff₀ hε).mpr (by linarith)
  have ho' : 1 ≤ (1-ε-‖z‖)/ε := (le_div_iff₀ hε).mpr (by linarith)
  simp [radialEnergyCutoff, energyUnitRamp_eq_one hi',
    energyUnitRamp_eq_one ho']

theorem radialEnergyCutoff_continuous {ε : ℝ} :
    Continuous (radialEnergyCutoff ε) := by
  unfold radialEnergyCutoff energyUnitRamp
  fun_prop

theorem energyUnitRamp_lipschitz : LipschitzWith 1 energyUnitRamp := by
  unfold energyUnitRamp
  convert (LipschitzWith.const (0 : ℝ)).max
      ((LipschitzWith.const (1 : ℝ)).min LipschitzWith.id) using 1
  · norm_num
  · rfl

/-- The two ramps together have Lipschitz constant at most 2/ε.
Consequently the same bound holds for the totalized real fderiv,
including points where the piecewise linear cutoff is not smooth. -/
theorem radialEnergyCutoff_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (⟨2/ε, by positivity⟩ : NNReal)
      (radialEnergyCutoff ε) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  let a := energyUnitRamp ((‖z‖-ε)/ε)
  let b := energyUnitRamp ((1-ε-‖z‖)/ε)
  let c := energyUnitRamp ((‖w‖-ε)/ε)
  let d := energyUnitRamp ((1-ε-‖w‖)/ε)
  have hnorm : |‖z‖-‖w‖| ≤ ‖z-w‖ := abs_norm_sub_norm_le z w
  have hac : |a-c| ≤ ‖z-w‖/ε := by
    have h := energyUnitRamp_lipschitz.dist_le_mul
      ((‖z‖-ε)/ε) ((‖w‖-ε)/ε)
    have heq : (‖z‖-ε)/ε-(‖w‖-ε)/ε = (‖z‖-‖w‖)/ε := by ring
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, heq,
      abs_div, abs_of_pos hε] at h
    exact h.trans (div_le_div_of_nonneg_right hnorm hε.le)
  have hbd : |b-d| ≤ ‖z-w‖/ε := by
    have h := energyUnitRamp_lipschitz.dist_le_mul
      ((1-ε-‖z‖)/ε) ((1-ε-‖w‖)/ε)
    have heq : (1-ε-‖z‖)/ε-(1-ε-‖w‖)/ε = -(‖z‖-‖w‖)/ε := by ring
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, heq,
      abs_div, abs_neg, abs_of_pos hε] at h
    exact h.trans (div_le_div_of_nonneg_right hnorm hε.le)
  have hb : |b| ≤ 1 := by
    rw [abs_of_nonneg (energyUnitRamp_bounds _).1]
    exact (energyUnitRamp_bounds _).2
  have hc : |c| ≤ 1 := by
    rw [abs_of_nonneg (energyUnitRamp_bounds _).1]
    exact (energyUnitRamp_bounds _).2
  have hprod : |a*b-c*d| ≤ |a-c|+|b-d| := by
    calc
      _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
      _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
      _ = |a-c| * |b| + |c| * |b-d| := by rw [abs_mul, abs_mul]
      _ ≤ |a-c| * 1 + 1 * |b-d| := by gcongr
      _ = _ := by ring
  change |a*b-c*d| ≤ (2/ε)*dist z w
  rw [dist_eq_norm]
  calc
    _ ≤ _ := hprod
    _ ≤ ‖z-w‖/ε+‖z-w‖/ε := add_le_add hac hbd
    _ = _ := by ring

theorem radialEnergyCutoff_fderiv_norm_le {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) : ‖fderiv ℝ (radialEnergyCutoff ε) z‖ ≤ 2/ε :=
  norm_fderiv_le_of_lipschitz ℝ (radialEnergyCutoff_lipschitz hε)

theorem radialEnergyCutoff_fderiv_zero_core {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hi : 2*ε < ‖z‖) (ho : ‖z‖ < 1-2*ε) :
    fderiv ℝ (radialEnergyCutoff ε) z = 0 := by
  have heq : radialEnergyCutoff ε =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℝ)) := by
    filter_upwards
      [continuous_norm.continuousAt.eventually (lt_mem_nhds hi),
       continuous_norm.continuousAt.eventually (gt_mem_nhds ho)]
      with w hw₁ hw₂
    exact radialEnergyCutoff_eq_one hε hw₁.le hw₂.le
  simpa using heq.fderiv_eq (𝕜 := ℝ)

theorem radialEnergyCutoff_eventually_fderiv_zero
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ∀ᶠ j in atTop, fderiv ℝ (radialEnergyCutoff (ε j)) z = 0 := by
  have hri : 0 < ‖z‖/2 := div_pos (norm_pos_iff.mpr hz0) (by norm_num)
  have hro : 0 < (1-‖z‖)/2 := by linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hri),
    hlim.eventually (gt_mem_nhds hro)] with j hi ho
  exact radialEnergyCutoff_fderiv_zero_core (hε j) (by linarith) (by linarith)

/-- At every noncentral point of the open disk, any positive widths
tending to zero eventually give cutoff value exactly one. -/
theorem radialEnergyCutoff_eventually_one
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ∀ᶠ j in atTop, radialEnergyCutoff (ε j) z = 1 := by
  have hri : 0 < ‖z‖/2 := div_pos (norm_pos_iff.mpr hz0) (by norm_num)
  have hro : 0 < (1-‖z‖)/2 := by linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hri),
    hlim.eventually (gt_mem_nhds hro)] with j hi ho
  exact radialEnergyCutoff_eq_one (hε j) (by linarith) (by linarith)

end
end SpringerLean

#print axioms SpringerLean.radialEnergyCutoff_eventually_one
