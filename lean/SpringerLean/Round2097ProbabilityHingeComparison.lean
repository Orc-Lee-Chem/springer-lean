import SpringerLean.Round1892LocalConvexGrid
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
open scoped BigOperators

namespace SpringerLean

/-- On a common compact interval, positive-part inequalities compare
all continuous nondecreasing convex tests of two actual probability laws. -/
theorem integral_mono_convex_of_hinges_on_Icc
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X Y : α → ℝ) (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y ν)
    (a b : ℝ) (hab : a < b)
    (hX : ∀ᵐ x ∂μ, X x ∈ Icc a b) (hY : ∀ᵐ x ∂ν, Y x ∈ Icc a b)
    (hhinge : ∀ c ∈ Icc a b, (∫ x, max (X x-c) 0 ∂μ) ≤ ∫ x, max (Y x-c) 0 ∂ν)
    (ψ : ℝ → ℝ) (hψc : Continuous ψ) (hψ : ConvexOn ℝ (Icc a b) ψ)
    (hmono : MonotoneOn ψ (Icc a b)) :
    (∫ x, ψ (X x) ∂μ) ≤ ∫ x, ψ (Y x) ∂ν := by
  have hci (ρ : Measure α) [IsProbabilityMeasure ρ]
      (V : α → ℝ) (hVm : AEMeasurable V ρ) (hV : ∀ᵐ x ∂ρ, V x ∈ Icc a b)
      (f : ℝ → ℝ) (hf : Continuous f) : Integrable (fun x => f (V x)) ρ := by
    obtain ⟨C,hC⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
    apply Integrable.mono (integrable_const (max C 0))
      (hf.measurable.comp_aemeasurable hVm).aestronglyMeasurable
    filter_upwards [hV] with x hx
    rw [Real.norm_of_nonneg (le_max_right C 0)]
    exact (hC _ ⟨V x,hx,rfl⟩).trans (le_max_left _ _)
  have hψX := hci μ X hXm hX ψ hψc
  have hψY := hci ν Y hYm hY ψ hψc
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨h,N,hh,htop,hw,happrox⟩ :=
    convex_exists_grid_hinge_uniform_local ψ hab hε hψ hψc.continuousOn
  let v : ℕ → ℝ := fun j => ψ (convexGridKnot a h j)
  let q := convexGridSlope v h 0
  let t : ℕ → ℝ := fun j => convexGridKnot a h (j+1)
  let w := convexGridWeight v h
  let G := convexGridHinge v a h N
  have hknot (j : ℕ) (hj : j ≤ N+1) : convexGridKnot a h j ∈ Icc a b := by
    refine ⟨?_, htop ▸ convexGridKnot_mono a hh.le hj⟩
    simpa [convexGridKnot] using convexGridKnot_mono a hh.le (Nat.zero_le j)
  have hzero : convexGridKnot a h 0 = a := by simp [convexGridKnot]
  have hq : 0 ≤ q := by
    unfold q convexGridSlope
    refine div_nonneg (sub_nonneg.mpr ?_) hh.le
    apply hmono (hknot 0 (by omega)) (hknot 1 (by omega))
    exact convexGridKnot_mono a hh.le (by omega)
  have hGcont : Continuous G := by unfold G convexGridHinge; fun_prop
  have hGX := hci μ X hXm hX G hGcont
  have hGY := hci ν Y hYm hY G hGcont
  have hrepr (ρ : Measure α) [IsProbabilityMeasure ρ]
      (Z : α → ℝ) (hZm : AEMeasurable Z ρ) (hZ : ∀ᵐ x ∂ρ, Z x ∈ Icc a b) :
      (∫ z, G (Z z) ∂ρ) = v 0+q*(∫ z, max (Z z-a) 0 ∂ρ) +
        ∑ i ∈ Finset.range N, w i*(∫ z, max (Z z-t i) 0 ∂ρ) := by
    have hi (c : ℝ) : Integrable (fun z => max (Z z-c) 0) ρ :=
      hci ρ Z hZm hZ (fun x => max (x-c) 0) (by fun_prop)
    have hlin : Integrable (fun z => v 0+q*max (Z z-a) 0) ρ :=
      (integrable_const _).add ((hi a).const_mul q)
    have hs (i : ℕ) : Integrable (fun z => w i*max (Z z-t i) 0) ρ := (hi (t i)).const_mul _
    have hsum := integrable_finsetSum (Finset.range N) (fun i _ => hs i)
    calc
      _ = ∫ z, v 0+q*max (Z z-a) 0 + ∑ i ∈ Finset.range N, w i*max (Z z-t i) 0 ∂ρ := by
        apply integral_congr_ae
        filter_upwards [hZ] with z hz
        change v 0+q*(Z z-a) + _ = _
        rw [max_eq_left (sub_nonneg.mpr hz.1)]
      _ = _ := by
        rw [integral_add hlin hsum, integral_add (integrable_const _) ((hi a).const_mul q),
          integral_const, probReal_univ, one_smul, integral_const_mul,
          integral_finsetSum _ (fun i _ => hs i)]
        simp_rw [integral_const_mul]
  have hpoly : (∫ x, G (X x) ∂μ) ≤ ∫ y, G (Y y) ∂ν := by
    rw [hrepr μ X hXm hX, hrepr ν Y hYm hY]
    apply add_le_add
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hhinge a ⟨le_rfl,hab.le⟩) hq)
    · apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_left (hhinge (t i) (hknot (i+1) (by omega))) (hw i hi')
  have hlo := integral_mono_ae hψX hGX (hX.mono fun x hx => (happrox (X x) hx).1)
  have hhi := integral_mono_ae hGY (hψY.add (integrable_const ε))
    (hY.mono fun y hy => (happrox (Y y) hy).2)
  change (∫ x, G (Y x) ∂ν) ≤ ∫ x, ψ (Y x)+ε ∂ν at hhi
  rw [integral_add hψY (integrable_const ε), integral_const, probReal_univ, one_smul] at hhi
  exact hlo.trans (hpoly.trans hhi)

end SpringerLean
