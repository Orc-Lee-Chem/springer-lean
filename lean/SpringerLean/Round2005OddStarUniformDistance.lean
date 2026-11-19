import SpringerLean.Round2004OddStarActualDerivativeIntegral
import Mathlib.Topology.Compactness.Compact

open Filter
open scoped Topology Filter

namespace SpringerLean

theorem oddStarBoundaryFactor_joint_continuousAt_zero
    (θ : ℝ) :
    ContinuousAt
      (fun p : ℝ × ℝ => oddStarBoundaryFactor
        (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1)
      (0, θ) := by
  let ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hζ : ζ ≠ 0 := Complex.exp_ne_zero _
  have hden :
      ((Real.sqrt (1 - (0 : ℝ) ^ 2) : ℂ) -
        ((0 : ℝ) : ℂ) * Complex.I) * ζ -
        ((0 : ℝ) : ℂ) * Complex.I ≠ 0 := by
    simpa using hζ
  unfold oddStarBoundaryFactor
  fun_prop (discharger := assumption)

theorem oddStarMovingBoundaryPoint_joint_continuousAt_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    ContinuousAt
      (fun p : ℝ × ℝ => oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m p.2) p.2 p.1)
      (0, θ) := by
  have hfactor := oddStarBoundaryFactor_joint_continuousAt_zero θ
  have hval : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) 0 = 1 := by
    simp [oddStarBoundaryFactor, Complex.exp_ne_zero]
  have hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) 0 ∈ Complex.slitPlane := by
    rw [hval, Complex.mem_slitPlane_iff]
    left
    norm_num
  have hlog := hfactor.clog hslit
  have hr : ContinuousAt (oddStarBoundaryRadius m) θ :=
    (oddStarBoundaryRadius_continuous m hm).continuousAt
  have hrjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarBoundaryRadius m p.2) (0, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.2) (0, θ) :=
      continuousAt_snd
    exact hr.comp hp
  change ContinuousAt (fun p : ℝ × ℝ =>
    (oddStarBoundaryRadius m p.2 : ℂ) * Complex.exp
      (((m : ℂ)⁻¹) * Complex.log
        (oddStarBoundaryFactor (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1)))
      (0, θ)
  fun_prop

theorem oddStarOppositeTipDistance_joint_continuousAt_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    ContinuousAt
      (fun p : ℝ × ℝ =>
        ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m p.2) p.2 p.1 -
          (oddStarTipRadius m p.1 : ℂ) *
            Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖)
      (0, θ) := by
  have hZ := oddStarMovingBoundaryPoint_joint_continuousAt_zero m hm θ
  have hR : ContinuousAt (oddStarTipRadius m) 0 :=
    (oddStarTipRadius_hasDerivAt_zero m hm).continuousAt
  have hRjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarTipRadius m p.1) (0, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.1) (0, θ) :=
      continuousAt_fst
    have hR' : ContinuousAt (oddStarTipRadius m)
        ((fun p : ℝ × ℝ => p.1) (0, θ)) := by
      simpa using hR
    exact hR'.comp hp
  fun_prop

theorem compact_uniform_lower_bound
    (K : Set ℝ) (hK : IsCompact K) (F : ℝ × ℝ → ℝ) (c : ℝ)
    (hcont : ∀ θ ∈ K, ContinuousAt F (0, θ))
    (hbase : ∀ θ ∈ K, c < F (0, θ)) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ K, c < F (t, θ) := by
  let S : Set (ℝ × ℝ) := {p | c < F p}
  have hs : S ∈ (𝓝 (0 : ℝ)) ×ˢ (𝓝ˢ K) := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro θ hθ
    have hmem : S ∈ 𝓝 (0, θ) :=
      (hcont θ hθ).eventually (eventually_gt_nhds (hbase θ hθ))
    simpa only [nhds_prod_eq] using hmem
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hs
  refine ⟨U, hU, ?_⟩
  intro t ht θ hθ
  exact hUV ⟨ht, (subset_of_mem_nhdsSet hV) hθ⟩

theorem oddStarOppositeTipDistance_uniform_local_lower_bound
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        oddStarTipRadius m 0 / 2 <
          ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
            (oddStarTipRadius m t : ℂ) *
              Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ := by
  let F : ℝ × ℝ → ℝ := fun p =>
    ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m p.2) p.2 p.1 -
      (oddStarTipRadius m p.1 : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖
  apply compact_uniform_lower_bound (Set.Icc (0 : ℝ) (2 * Real.pi))
    isCompact_Icc F (oddStarTipRadius m 0 / 2)
  · intro θ hθ
    exact oddStarOppositeTipDistance_joint_continuousAt_zero m hm θ
  · intro θ hθ
    have hRpos : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
    have hdist := oddStarOppositeTip_distance_ge_tipRadius m hm θ
    dsimp [F]
    linarith

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipDistance_uniform_local_lower_bound
