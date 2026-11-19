import SpringerLean.Round14QuadraticPrelude
import Mathlib.Analysis.Complex.JensenFormula

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A value on the actual regularized boundary curve has exactly one zero
of its potential factor in the closed disk, at the reciprocal boundary point. -/
theorem regularBoundaryPotential_zero_unique_of_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : ‖v‖ = 1)
    {u : ℂ} (hu : ‖u‖ ≤ 1)
    (hq : regularBoundaryPotential s F (rescaleExterior s F v) u = 0) :
    u = v⁻¹ := by
  have hu0 : u ≠ 0 := by
    intro hz
    subst u
    simp at hq
  have hunorm : 1 ≤ ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hu0)).mpr hu
  have hext : u⁻¹ ∈ exteriorAbove s := by
    change s < ‖u⁻¹‖
    exact lt_of_lt_of_le hs1 hunorm
  have hvext : v ∈ exteriorAbove s := by
    change s < ‖v‖
    rw [hv]
    exact hs1
  have heq : rescaleExterior s F u⁻¹ = rescaleExterior s F v := by
    rw [regularBoundaryPotential_punctured F hs0 _ hu0] at hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hu0)
  have hinj := rescaleExterior_injOn hs0 hc.2.1
  have huinv : u⁻¹ = v := hinj hext hvext heq
  calc
    u = (u⁻¹)⁻¹ := by simp
    _ = v⁻¹ := congrArg Inv.inv huinv

/-- A value on the actual regularized boundary curve gives no zeros in the
open disk. The single possible zero has norm one. -/
theorem regularBoundaryPotential_ne_zero_openDisk_of_boundary
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : ‖v‖ = 1)
    {u : ℂ} (hu : ‖u‖ < 1) :
    regularBoundaryPotential s F (rescaleExterior s F v) u ≠ 0 := by
  intro hq
  have heq := regularBoundaryPotential_zero_unique_of_boundary F hc hs0 hs1 hv hu.le hq
  have hnorm : ‖u‖ = 1 := by rw [heq, norm_inv, hv, inv_one]
  linarith

/-- For an actual image value, the reciprocal preimage is the only zero of
the potential factor even on the closed integration disk. -/
theorem regularBoundaryPotential_zero_unique_of_image_closedDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk)
    {u : ℂ} (hu : ‖u‖ ≤ 1)
    (hq : regularBoundaryPotential s F (rescaleExterior s F v) u = 0) :
    u = v⁻¹ := by
  have hu0 : u ≠ 0 := by
    intro hz
    subst u
    simp at hq
  have hunorm : 1 ≤ ‖u⁻¹‖ := by
    rw [norm_inv]
    exact (one_le_inv₀ (norm_pos_iff.mpr hu0)).mpr hu
  have hext : u⁻¹ ∈ exteriorAbove s := by
    change s < ‖u⁻¹‖
    exact lt_of_lt_of_le hs1 hunorm
  have hvext : v ∈ exteriorAbove s := by
    change s < ‖v‖
    exact lt_trans hs1 hv
  have heq : rescaleExterior s F u⁻¹ = rescaleExterior s F v := by
    rw [regularBoundaryPotential_punctured F hs0 _ hu0] at hq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left hu0)
  have hinj := rescaleExterior_injOn hs0 hc.2.1
  have huinv : u⁻¹ = v := hinj hext hvext heq
  calc
    u = (u⁻¹)⁻¹ := by simp
    _ = v⁻¹ := congrArg Inv.inv huinv

end SpringerLean
