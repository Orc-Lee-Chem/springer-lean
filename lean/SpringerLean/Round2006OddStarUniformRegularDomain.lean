import SpringerLean.Round2005OddStarUniformDistance

namespace SpringerLean
open scoped Topology

/-- The explicit boundary factor stays in the right half-plane on
one parameter neighborhood shared by every angle. -/
theorem oddStarBoundaryFactor_uniform_right_halfplane :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        (1 / 2 : ℝ) <
          (oddStarBoundaryFactor
            (Complex.exp ((θ : ℂ) * Complex.I)) t).re := by
  let F : ℝ × ℝ → ℝ := fun p =>
    (oddStarBoundaryFactor
      (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1).re
  apply compact_uniform_lower_bound (Set.Icc (0 : ℝ) (2 * Real.pi))
    isCompact_Icc F (1 / 2 : ℝ)
  · intro θ hθ
    exact Complex.continuous_re.continuousAt.comp
      (oddStarBoundaryFactor_joint_continuousAt_zero θ)
  · intro θ hθ
    dsimp [F]
    simp [oddStarBoundaryFactor, Complex.exp_ne_zero]
    norm_num

theorem oddStarBoundaryFactor_denominator_ne_zero_of_re_pos
    (ζ : ℂ) (t : ℝ)
    (h : 0 < (oddStarBoundaryFactor ζ t).re) :
    ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * ζ -
      (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hf : oddStarBoundaryFactor ζ t = 0 := by
    simp [oddStarBoundaryFactor, hzero]
  rw [hf] at h
  norm_num at h

theorem oddStarBoundaryFactor_alpha_ne_zero_of_re_pos
    (ζ : ℂ) (t : ℝ)
    (h : 0 < (oddStarBoundaryFactor ζ t).re) :
    (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hf : oddStarBoundaryFactor ζ t = 0 := by
    simp [oddStarBoundaryFactor, hzero]
  rw [hf] at h
  norm_num at h

theorem oddStarBoundaryFactor_uniform_log_domain :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        (oddStarBoundaryFactor
          (Complex.exp ((θ : ℂ) * Complex.I)) t) ∈ Complex.slitPlane ∧
        ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
          Complex.exp ((θ : ℂ) * Complex.I) -
          (t : ℂ) * Complex.I ≠ 0 ∧
        (Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I ≠ 0 := by
  obtain ⟨U, hU, hpos⟩ := oddStarBoundaryFactor_uniform_right_halfplane
  refine ⟨U, hU, ?_⟩
  intro t ht θ hθ
  have hhalf := hpos t ht θ hθ
  have h : 0 < (oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t).re := by
    linarith
  exact ⟨Complex.mem_slitPlane_iff.mpr (Or.inl h),
    oddStarBoundaryFactor_denominator_ne_zero_of_re_pos _ t h,
    oddStarBoundaryFactor_alpha_ne_zero_of_re_pos _ t h⟩

theorem oddStarVariation_uniform_regular_domain
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        oddStarTipRadius m 0 / 2 <
          ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
            (oddStarTipRadius m t : ℂ) *
              Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ ∧
        (oddStarBoundaryFactor
          (Complex.exp ((θ : ℂ) * Complex.I)) t) ∈ Complex.slitPlane ∧
        ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
          Complex.exp ((θ : ℂ) * Complex.I) -
          (t : ℂ) * Complex.I ≠ 0 := by
  obtain ⟨U, hU, hdist⟩ :=
    oddStarOppositeTipDistance_uniform_local_lower_bound m hm
  obtain ⟨V, hV, hlog⟩ := oddStarBoundaryFactor_uniform_log_domain
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht θ hθ
  exact ⟨hdist t ht.1 θ hθ, (hlog t ht.2 θ hθ).1,
    (hlog t ht.2 θ hθ).2.1⟩

end SpringerLean

#print axioms SpringerLean.oddStarVariation_uniform_regular_domain
