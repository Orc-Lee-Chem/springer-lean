import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

/-- Integrability of the radial derivative gives a limit along all radii,
not merely along a subsequence.  The endpoint is an ordinary Bochner
primitive, so no boundary value is assumed in the statement. -/
theorem tendsto_left_endpoint_of_integrable_deriv
    {f f' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ r ∈ Ico a b, HasDerivAt f (f' r) r)
    (hint : IntegrableOn f' (Ioo a b)) :
    Tendsto f (𝓝[<] b) (𝓝 (f a + ∫ t in a..b, f' t)) := by
  have hi : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hint
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (left_mem_uIcc : a ∈ uIcc a b)
  have hnear : ∀ᶠ r in 𝓝[<] b, a ≤ r ∧ r < b := by
    filter_upwards [Ioo_mem_nhdsLT hab] with r hr
    exact ⟨hr.1.le, hr.2⟩
  have ht : Tendsto (fun r : ℝ => r) (𝓝[<] b) (𝓝[uIcc a b] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hnear] with r hr
    simpa only [uIcc_of_le hab.le] using (show r ∈ Icc a b from ⟨hr.1, hr.2.le⟩)
  have hp := (hc b right_mem_uIcc).tendsto.comp ht
  have hs := (tendsto_const_nhds (x := f a)).add hp
  apply hs.congr'
  filter_upwards [hnear] with r hr
  have hir : IntervalIntegrable f' volume a r := hi.mono_set (by
    rw [uIcc_of_le hr.1, uIcc_of_le hab.le]
    exact Icc_subset_Icc le_rfl hr.2.le)
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by
      rw [uIcc_of_le hr.1] at ht
      exact ⟨ht.1, ht.2.trans_lt hr.2⟩)) hir
  change f a + (∫ t in a..r, f' t) = f r
  rw [heq]
  abel

end SpringerLean

#print axioms SpringerLean.tendsto_left_endpoint_of_integrable_deriv
