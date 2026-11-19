import SpringerLean.Round2106PeriodicTopIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

open Set MeasureTheory Real

namespace SpringerLean

/-- A measurable angular level inside one turn can be sliced to any
prescribed measure by moving its right endpoint. -/
theorem exists_angular_level_slice (A : Set ℝ) (hA : MeasurableSet A)
    {a b m : ℝ} (hab : a ≤ b) (hsub : A ⊆ Ioc a b)
    (hm : 0 ≤ m) (hvol : m ≤ volume.real A) :
    ∃ c ∈ Icc a b, volume.real (A ∩ Ioc a c) = m := by
  let f : ℝ → ℝ := A.indicator (fun _ => 1)
  let L (x : ℝ) := ∫ t in a..x, f t
  have hInt (x y : ℝ) : IntervalIntegrable f volume x y := by
    refine ⟨?_,?_⟩
    · exact (show IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc x y) from
        integrableOn_const (Metric.isBounded_Ioc x y).measure_lt_top.ne).indicator hA
    · exact (show IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioc y x) from
        integrableOn_const (Metric.isBounded_Ioc y x).measure_lt_top.ne).indicator hA
  have hL : Continuous L := intervalIntegral.continuous_primitive hInt a
  have hEq (c : ℝ) (hc : a ≤ c) : L c = volume.real (A ∩ Ioc a c) := by
    unfold L f
    rw [intervalIntegral.integral_of_le hc, integral_indicator hA, Measure.restrict_restrict hA,
      integral_const, smul_eq_mul,measureReal_restrict_apply_univ,mul_one]
  have hLeft : L a = 0 := by simp [L]
  have hRight : L b = volume.real A := by rw [hEq b hab,inter_eq_left.mpr hsub]
  have hmem : m ∈ Icc (L a) (L b) := by rw [hLeft,hRight]; exact ⟨hm,hvol⟩
  obtain ⟨c,hc,hval⟩ := intermediate_value_Icc hab hL.continuousOn hmem
  exact ⟨c,hc,(hEq c hc.1).symm.trans hval⟩

end SpringerLean
