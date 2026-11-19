import SpringerLean.Round2094FilledContinuumTopology
import Mathlib.Topology.Compactification.OnePoint.Basic

open Set
open scoped OnePoint

namespace SpringerLean

/-- If the spherical complement of a plane set is connected, filling
any compact subset stays inside the set. This applies in particular
to the trace of a loop in the set. -/
theorem continuumFill_subset_of_sphere_compl_preconnected
    {U P : Set ℂ} (hP : IsCompact P) (hsub : P ⊆ U)
    (hc : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' U)ᶜ) :
    continuumFill P ⊆ U := by
  let C := (((↑) : ℂ → OnePoint ℂ) '' U)ᶜ
  let L := continuumFill P
  let O := (((↑) : ℂ → OnePoint ℂ) '' L)ᶜ
  let B := ((↑) : ℂ → OnePoint ℂ) '' (L \ P)
  have hLc := isClosed_continuumFill P hP.isClosed
  have hLB := isBounded_continuumFill P hP
  have hL : IsCompact L := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hLc,hLB⟩
  have hO : IsOpen O := OnePoint.isOpen_compl_image_coe.mpr ⟨hLc,hL⟩
  have hB : IsOpen B := by
    apply OnePoint.isOpen_image_coe.mpr
    have h : L \ P = interior L \ P :=
      Subset.antisymm (fun _ hz => ⟨continuumFill_diff_subset_interior P hP.isClosed hz,hz.2⟩)
        (fun _ hz => ⟨interior_subset hz.1,hz.2⟩)
    rw [h]
    exact isOpen_interior.sdiff hP.isClosed
  have hd : Disjoint O B := by
    rw [Set.disjoint_left]
    rintro _ ho ⟨z,hz,rfl⟩
    exact ho ⟨z,hz.1,rfl⟩
  have hcov : C ⊆ O ∪ B := by
    intro w hw
    by_cases ho : w ∈ O
    · exact Or.inl ho
    · obtain ⟨z,hz,rfl⟩ : w ∈ ((↑) : ℂ → OnePoint ℂ) '' L := not_not.mp ho
      exact Or.inr ⟨z,⟨hz,fun hp => hw ⟨z,hsub hp,rfl⟩⟩,rfl⟩
  have hN : (C ∩ O).Nonempty := ⟨∞,OnePoint.infty_notMem_image_coe,OnePoint.infty_notMem_image_coe⟩
  have ho := hc.subset_left_of_subset_union hO hB hd hcov hN
  intro z hz
  by_contra h
  have hw : (z:OnePoint ℂ) ∈ C := by
    rintro ⟨w,hw,he⟩
    exact h (OnePoint.coe_injective he ▸ hw)
  exact ho hw ⟨z,hz,rfl⟩

end SpringerLean
