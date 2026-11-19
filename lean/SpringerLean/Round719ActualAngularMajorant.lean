import SpringerLean.Round717ActualAngularLocalSubmean
import SpringerLean.Round718CompactCircleMaximum

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The unnormalized centered-arc integral of the slit comparator in
logarithmic radius and angular half-mass. -/
noncomputable def angularSineMajorant (c z : ℂ) : ℝ :=
  4*‖c‖*(Complex.exp z).im

theorem angularSineMajorant_coordinates (c z : ℂ) :
    angularSineMajorant c z = 4*‖c‖*Real.exp z.re*Real.sin z.im := by
  rw [angularSineMajorant, Complex.exp_im]
  ring

theorem angularSineMajorant_continuous (c : ℂ) :
    Continuous (angularSineMajorant c) := by
  unfold angularSineMajorant
  fun_prop

theorem angularSineMajorant_harmonicOnNhd (c : ℂ) :
    InnerProductSpace.HarmonicOnNhd (angularSineMajorant c) (univ : Set ℂ) := by
  intro z hz
  have ha : AnalyticAt ℂ (fun w : ℂ => ((4*‖c‖ : ℝ) : ℂ)*Complex.exp w) z :=
    analyticAt_const.mul analyticAt_cexp
  convert ha.harmonicAt_im using 1
  funext w
  simp [angularSineMajorant]

theorem angularSineMajorant_circleAverage (c z : ℂ) (ρ : ℝ) :
    Real.circleAverage (angularSineMajorant c) z ρ = angularSineMajorant c z := by
  exact ((angularSineMajorant_harmonicOnNhd c).mono (subset_univ _)).circleAverage_eq

/-- Subtracting the explicit harmonic comparator preserves the actual
local submean.  No boundary comparison is assumed or concluded here. -/
theorem logarithmicActualTopValue_sub_majorant_local_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c z : ℂ)
    (hx : z.re < 0) (hh0 : 0 < z.im) (hhpi : z.im < Real.pi) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      logarithmicActualTopValue F c z-angularSineMajorant c z ≤
        Real.circleAverage
          (fun w : ℂ => logarithmicActualTopValue F c w-angularSineMajorant c w) z ρ := by
  obtain ⟨d, hd, hs⟩ := logarithmicActualTopValue_local_circle_submean F hc c z hx hh0 hhpi
  let r₀ := min d (min (-z.re) (min z.im (Real.pi-z.im)))
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min hd (lt_min (neg_pos.mpr hx) (lt_min hh0 (sub_pos.mpr hhpi)))
  refine ⟨r₀, hr₀, ?_⟩
  intro ρ hρ hρr
  have hρd : ρ < d := hρr.trans_le (min_le_left _ _)
  have hρx : ρ < -z.re := hρr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρh : ρ < z.im := hρr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρpi : ρ < Real.pi-z.im := hρr.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hSci := logarithmicActualTopValue_circleIntegrable F hc c hρ.le hρx hρh hρpi
  have hMci : CircleIntegrable (angularSineMajorant c) z ρ :=
    (angularSineMajorant_continuous c).continuousOn.circleIntegrable hρ.le
  rw [Real.circleAverage_fun_sub hSci hMci, angularSineMajorant_circleAverage]
  exact sub_le_sub_right (hs ρ hρ hρd) _

/-- A compact-domain comparison for the SAME actual F.  The boundary
estimate is explicit in this development interface; the future global
inner-circle statement must discharge it at all four rectangle edges. -/
theorem logarithmicActualTopValue_le_majorant_on_compact
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    (K : Set ℂ) (hK : IsCompact K)
    (hsub : K ⊆ {z : ℂ | z.re < 0 ∧ 0 < z.im ∧ z.im < Real.pi})
    (M : ℝ) (hb : ∀ z ∈ frontier K,
      logarithmicActualTopValue F c z-angularSineMajorant c z ≤ M) :
    ∀ z ∈ K, logarithmicActualTopValue F c z ≤ angularSineMajorant c z+M := by
  have hu : ContinuousOn
      (fun z : ℂ => logarithmicActualTopValue F c z-angularSineMajorant c z) K :=
    ((logarithmicActualTopValue_continuousOn F hc c).mono hsub).sub
      (angularSineMajorant_continuous c).continuousOn
  have hmax := le_of_local_circle_submean_of_compact
    (fun z : ℂ => logarithmicActualTopValue F c z-angularSineMajorant c z) K hK hu
    (by
      intro z hz
      have hs := hsub (interior_subset hz)
      exact logarithmicActualTopValue_sub_majorant_local_circle_submean F hc c z hs.1 hs.2.1 hs.2.2)
    M hb
  intro z hz
  have hv := hmax z hz
  linarith

end SpringerLean

#print axioms SpringerLean.angularSineMajorant_circleAverage
#print axioms SpringerLean.logarithmicActualTopValue_sub_majorant_local_circle_submean
#print axioms SpringerLean.logarithmicActualTopValue_le_majorant_on_compact
