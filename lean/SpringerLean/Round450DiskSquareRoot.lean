import SpringerLean.DiskExpansion
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Filter
open scoped Topology

namespace SpringerLean

/-- A normalized analytic square root on the actual unit disk. No square-root
or local inverse hypothesis is supplied by callers. -/
theorem analyticOnNhd_unitBall_exists_normalized_square_root
    (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) 1))
    (hg0 : g 0 = 1) (hne : ∀ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (Metric.ball (0 : ℂ) 1) ∧
      R 0 = 1 ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, R z ^ 2 = g z := by
  have hs : IsSimplyConnected (Metric.ball (0 : ℂ) 1) := by
    letI : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
      (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
    change SimplyConnectedSpace (Metric.ball (0 : ℂ) 1)
    infer_instance
  have hno : 0 ∉ g '' Metric.ball (0 : ℂ) 1 := by
    rintro ⟨z, hz, he⟩
    exact hne z hz he
  obtain ⟨Q, hQc, hQpow⟩ := Complex.exists_continuousOn_pow_eq hs Metric.isOpen_ball
    hg.continuousOn hno (n := 2) (by norm_num)
  have hQnz (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : Q z ≠ 0 := by
    intro hzero
    have h := hQpow z
    rw [hzero, zero_pow (by omega : (2 : ℕ) ≠ 0)] at h
    exact hne z hz h.symm
  have hQd : DifferentiableOn ℂ Q (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hp : HasDerivAt (fun w : ℂ => w ^ 2) (2 * Q z) (Q z) := by
      convert (hasDerivAt_id (Q z)).pow 2 using 1 <;> first | rfl | simp
    have heq : (fun w : ℂ => w ^ 2) ∘ Q =ᶠ[𝓝 z] g :=
      Filter.Eventually.of_forall hQpow
    exact (HasDerivAt.of_comp_left
      (hQc.continuousAt (Metric.isOpen_ball.mem_nhds hz)) hp
      (hg z hz).differentiableAt.hasDerivAt
      (mul_ne_zero (by norm_num) (hQnz z hz)) heq).differentiableAt.differentiableWithinAt
  have hQa : AnalyticOnNhd ℂ Q (Metric.ball (0 : ℂ) 1) :=
    fun z hz => hQd.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hQ0 : Q 0 ≠ 0 := hQnz 0 (by simp)
  have hQ02 : Q 0 ^ 2 = 1 := (hQpow 0).trans hg0
  refine ⟨fun z => Q z / Q 0, ?_, div_self hQ0, ?_⟩
  · intro z hz
    exact (hQa z hz).div_const
  · intro z hz
    rw [div_pow, hQpow z, hQ02, div_one]

end SpringerLean
