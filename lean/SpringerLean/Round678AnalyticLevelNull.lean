import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Filter MeasureTheory

namespace SpringerLean
set_option Elab.async false

/-- A nonconstant globally real-analytic function has no positive-mass
level. This uses the proved analytic identity principle, then the
codiscrete-to-a.e. interface for atomless Lebesgue measure. -/
theorem analyticOn_real_level_ae_ne
    (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (hnot : ¬ ∃ c : ℝ, ∀ t : ℝ, f t=c) (c : ℝ) :
    ∀ᵐ t : ℝ ∂volume, f t ≠ c := by
  have hc : AnalyticOnNhd ℝ (fun _ : ℝ => c) Set.univ :=
    fun _ _ => analyticAt_const
  rcases hf.eqOn_or_eventually_ne_of_preconnected hc isPreconnected_univ with h | h
  · exact (hnot ⟨c,fun t => h (Set.mem_univ t)⟩).elim
  · have hle : ae (volume : Measure ℝ) ≤ codiscreteWithin (Set.univ : Set ℝ) := by
      simpa only [Measure.restrict_univ] using
        (ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ)
    exact hle h

theorem analyticOn_real_level_volume_zero
    (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (hnot : ¬ ∃ c : ℝ, ∀ t : ℝ, f t=c) (c : ℝ) :
    volume {t : ℝ | f t=c}=0 := by
  simpa only [ne_eq,not_not] using
    (ae_iff.mp (analyticOn_real_level_ae_ne f hf hnot c))

end SpringerLean
