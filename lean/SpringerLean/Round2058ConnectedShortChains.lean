import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Logic.Relation

open Set Metric Relation
open scoped Topology

namespace SpringerLean

/-- Two points in a connected metric space can be joined by finitely
many steps shorter than any prescribed positive length. This is the
only connectivity of the omitted set needed for local logarithms of
root ratios. -/
theorem preconnected_reflTransGen_dist_lt {E : Type*} [PseudoMetricSpace E]
    [PreconnectedSpace E] (a b : E) {ε : ℝ} (hε : 0 < ε) :
    ReflTransGen (fun x y : E => dist x y < ε) a b := by
  let s : Set E := {x | ReflTransGen (fun x y : E => dist x y < ε) a x}
  have hsOpen : IsOpen s := by
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    exact (show ReflTransGen (fun x y : E => dist x y < ε) a x from hx).tail
      (by simpa [dist_comm] using Metric.mem_ball.mp hy)
  have hcOpen : IsOpen sᶜ := by
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨ε, hε, ?_⟩
    intro y hy hy'
    apply hx
    exact (show ReflTransGen (fun x y : E => dist x y < ε) a y from hy').tail
      (Metric.mem_ball.mp hy)
  have hs : IsClopen s := ⟨isOpen_compl_iff.mp hcOpen, hsOpen⟩
  have ha : a ∈ s := ReflTransGen.refl
  have hb : b ∈ s := by
    rcases isClopen_iff.mp hs with h | h
    · simp [h] at ha
    · simp [h]
  exact hb

end SpringerLean
