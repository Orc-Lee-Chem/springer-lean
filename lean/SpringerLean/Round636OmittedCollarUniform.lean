import SpringerLean.Round632OmittedSequentialLimit
import SpringerLean.Round480OmittedRadius

open Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false

/-- Continuous inequalities on a closed part of the actual omitted set
transfer uniformly to the genuine regularized omitted sets, with arbitrary
positive error. This avoids imposing radial boundary values on F. -/
theorem exteriorOmitted_rescale_inequality_eventually_scaleSeq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (C : Set ℂ) (hC : IsClosed C) (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hK : ∀ w ∈ exteriorOmitted F, w ∈ C → ψ w ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ exteriorOmitted (rescaleExterior (omittedScaleSeq n) F),
        w ∈ C → ψ w ≤ ε := by
  classical
  by_contra h
  simp only [Filter.eventually_atTop] at h
  push_neg at h
  choose k hk w hwK hwC hwbad using h
  have hkTop : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop N] with j hj
    exact hj.trans (hk j)
  have hball (j : ℕ) : w j ∈ Metric.closedBall (0 : ℂ) 2 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using
      exteriorOmitted_norm_le_two _
        (rescaleExterior_centeredExteriorUnivalent F hc
          (omittedScaleSeq_pos (k j)) (omittedScaleSeq_lt_one (k j))) (hwK j)
  obtain ⟨v,hvball,φ,hφmono,hφlim⟩ :=
    (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq hball
  have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hs : Tendsto (fun j => omittedScaleSeq (k (φ j))) atTop (𝓝 (1 : ℝ)) :=
    (omittedScaleSeq_tendsto_one.comp hkTop).comp hφtop
  have hvK : v ∈ exteriorOmitted F :=
    exteriorOmitted_rescale_mem_of_tendsto F hc hs
      (Eventually.of_forall (fun j => hwK (φ j))) hφlim
  have hvC : v ∈ C :=
    hC.mem_of_tendsto hφlim (Eventually.of_forall (fun j => hwC (φ j)))
  have hψlim : Tendsto (fun j => ψ (w (φ j))) atTop (𝓝 (ψ v)) :=
    (hψ.tendsto v).comp hφlim
  have hvbad : ε ≤ ψ v := le_of_tendsto_of_tendsto
    tendsto_const_nhds hψlim (Eventually.of_forall (fun j => (hwbad (φ j)).le))
  have hvle := hK v hvK hvC
  linarith

end SpringerLean
