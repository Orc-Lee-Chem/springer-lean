import SpringerLean.Round686ActualAngularOptimizer

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- Candidates in one turn, with RAW length2h. The definition records only
measurability, location and mass, and contains no mathematical conclusion. -/
noncomputable def angularTopFeasible (h : ℝ) : Set (Set ℝ) :=
  {E | MeasurableSet E ∧ E ⊆ Ioc 0 (2*Real.pi) ∧
    volume E = ENNReal.ofReal (2*h)}

/-- The top-mass integral of the SAME actual harmonic filling. -/
noncomputable def actualAngularTopValue (F : ℂ → ℂ) (c : ℂ) (r h : ℝ) : ℝ :=
  sSup ((fun E : Set ℝ =>
    ∫ θ in E, (c*actualHarmonic F (circleMap 0 r θ)).re) '' angularTopFeasible h)

theorem actualAngularTopValue_attained
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ E ∈ angularTopFeasible h,
      actualAngularTopValue F c r h =
        (∫ θ in E, (c*actualHarmonic F (circleMap 0 r θ)).re) ∧
      ∀ A ∈ angularTopFeasible h,
        (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤
          ∫ θ in E, (c*actualHarmonic F (circleMap 0 r θ)).re := by
  obtain ⟨E, hEm, hEsub, hEmass, hmax⟩ :=
    actualHarmonic_angular_projection_exists_maximizer F hc c hr0 hr1 hh0 hhpi
  have hEf : E ∈ angularTopFeasible h := ⟨hEm, hEsub, hEmass⟩
  let costs : Set ℝ := (fun A : Set ℝ =>
    ∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) '' angularTopFeasible h
  let M : ℝ := ∫ θ in E, (c*actualHarmonic F (circleMap 0 r θ)).re
  have hMmem : M ∈ costs := ⟨E, hEf, rfl⟩
  have hupper : ∀ v ∈ costs, v ≤ M := by
    rintro v ⟨A, hAf, rfl⟩
    exact hmax A hAf.1 hAf.2.1 hAf.2.2
  have hval : actualAngularTopValue F c r h = M :=
    le_antisymm (csSup_le ⟨M, hMmem⟩ hupper) (le_csSup ⟨M, hupper⟩ hMmem)
  refine ⟨E, hEf, hval, ?_⟩
  intro A hAf
  exact hmax A hAf.1 hAf.2.1 hAf.2.2

theorem actualAngularTopValue_candidate_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (A : Set ℝ) (hA : A ∈ angularTopFeasible h) :
    (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤
      actualAngularTopValue F c r h := by
  obtain ⟨E, hE, hval, hmax⟩ := actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
  rw [hval]
  exact hmax A hA

/-- A true, coarse bound on the actual top value. It is useful on the
far left edge in logarithmic coordinates; the sharp4r*sin(h) comparison
still requires the local star-function argument. -/
theorem actualAngularTopValue_abs_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    |actualAngularTopValue F c r h| ≤ 4*‖c‖*r*h := by
  obtain ⟨E, hE, hval, hmax⟩ := actualAngularTopValue_attained F hc c hr0 hr1 hh0 hhpi
  have hfin : volume E < ∞ := by rw [hE.2.2]; finiteness
  have hreal : volume.real E = 2*h := by
    rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith : 0 ≤ 2*h)]
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := E)
    (f := fun θ => (c*actualHarmonic F (circleMap 0 r θ)).re) hfin
    (fun θ _ => by simpa only [Real.norm_eq_abs] using
      actualHarmonic_angular_projection_abs_le F hc c hr0 hr1 θ)
  rw [hval]
  simpa only [Real.norm_eq_abs, hreal, show ‖c‖*(2*r)*(2*h) = 4*‖c‖*r*h by ring]
    using hbound

end SpringerLean
