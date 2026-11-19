import SpringerLean.Round698ActualTopJointContinuity
import Mathlib.Analysis.Complex.Circle

open MeasureTheory Set Metric
open scoped Topology

namespace SpringerLean
set_option Elab.async false

/-- Logarithmic coordinates for the actual top-mass integral. Here im(z)
is the HALF-MASS parameter, not an angular integration variable. -/
noncomputable def logarithmicActualTopValue (F : ℂ → ℂ) (c z : ℂ) : ℝ :=
  actualAngularTopValue F c (Real.exp z.re) z.im

theorem logarithmicActualTopValue_continuousOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) :
    ContinuousOn (logarithmicActualTopValue F c)
      {z : ℂ | z.re < 0 ∧ 0 < z.im ∧ z.im < Real.pi} := by
  intro z hz
  have hexp : Real.exp z.re < 1 := Real.exp_lt_one_iff.mpr hz.1
  obtain ⟨R, hrR, hR1⟩ := exists_between hexp
  have hR0 : 0 ≤ R := le_of_lt ((Real.exp_pos z.re).trans hrR)
  have hcont := actualAngularTopValue_continuousOn_subrectangle F hc c hR0 hR1
  have hcontOpen : ContinuousOn
      (fun p : ℝ × ℝ => actualAngularTopValue F c p.1 p.2)
      (Ioo 0 R ×ˢ Ioo 0 Real.pi) :=
    hcont.mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  have hp : (Real.exp z.re, z.im) ∈ Ioo 0 R ×ˢ Ioo 0 Real.pi :=
    ⟨⟨Real.exp_pos _, hrR⟩, hz.2⟩
  have hAt := hcontOpen.continuousAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)
  have hpair : ContinuousAt (fun w : ℂ => (Real.exp w.re, w.im)) z := by fun_prop
  have hcomposed : ContinuousAt
      (fun w : ℂ => actualAngularTopValue F c (Real.exp w.re) w.im) z :=
    hAt.comp (f := fun w : ℂ => (Real.exp w.re, w.im)) (x := z) hpair
  exact hcomposed.continuousWithinAt

private theorem logarithmicTop_sphere_subset
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρx : ρ < -z.re) (hρy : ρ < z.im) (hρpi : ρ < Real.pi-z.im) :
    sphere z |ρ| ⊆ {w : ℂ | w.re < 0 ∧ 0 < w.im ∧ w.im < Real.pi} := by
  intro w hw
  have hn : ‖w-z‖ = ρ := by
    simpa only [mem_sphere, dist_eq_norm, abs_of_nonneg hρ0] using hw
  have hre : |w.re-z.re| ≤ ρ := by
    simpa only [Complex.sub_re, hn] using Complex.abs_re_le_norm (w-z)
  have him : |w.im-z.im| ≤ ρ := by
    simpa only [Complex.sub_im, hn] using Complex.abs_im_le_norm (w-z)
  change w.re < 0 ∧ 0 < w.im ∧ w.im < Real.pi
  obtain ⟨hrelo, hrehi⟩ := abs_le.mp hre
  obtain ⟨himlo, himhi⟩ := abs_le.mp him
  constructor
  · linarith
  · constructor <;> linarith

/-- Circle integrability of the actual star functional is proved from
its actual optimizer/continuity interfaces. Local submean remains a
separate theorem, so no circular assumption enters this declaration. -/
theorem logarithmicActualTopValue_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {z : ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρx : ρ < -z.re) (hρy : ρ < z.im) (hρpi : ρ < Real.pi-z.im) :
    CircleIntegrable (logarithmicActualTopValue F c) z ρ := by
  exact ((logarithmicActualTopValue_continuousOn F hc c).mono
    (logarithmicTop_sphere_subset hρ0 hρx hρy hρpi)).circleIntegrable'

end SpringerLean
