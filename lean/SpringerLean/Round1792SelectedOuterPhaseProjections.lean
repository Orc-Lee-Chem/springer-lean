import SpringerLean.Round1791OppositeOuterProjection

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 500000

theorem unit_ray_distance_small
    (ξ v : ℂ) (hξ : ‖ξ‖=1) {δ : ℝ}
    (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I))
    {k : ℕ} (hk : 751 ≤ k) (hδ : |δ| ≤ Real.pi/(2*(k : ℝ))) :
    ‖v-ξ‖ ≤ 1/200 := by
  have hdiff : v-ξ=ξ*(Complex.exp (Complex.I*(δ : ℂ))-1) := by
    rw [hv, mul_comm Complex.I (δ : ℂ)]
    ring
  have hdist : ‖v-ξ‖ ≤ |δ| := by
    rw [hdiff, norm_mul, hξ, one_mul]
    simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := δ))
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hshort : Real.pi/(2*(k : ℝ)) ≤ 1/200 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(k : ℝ))).mpr
    linarith [Real.pi_lt_four]
  exact hdist.trans (hδ.trans hshort)

/-- Both original assigned outer halves now have positive projection
in their own recorded nearby phase ray. The tangent is allowed in
both hypotheses; no null-level-set assumption is used. -/
theorem ActualCandidatePhaseEndpoints.outer_projections
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    (∀ w ∈ convexHull ℝ (exteriorOmitted F), (46/25 : ℝ) ≤ ‖w‖ →
      0 ≤ (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*w).re →
      (9/5 : ℝ) < (conj ends.v₁*w).re) ∧
    (∀ w ∈ convexHull ℝ (exteriorOmitted F), (46/25 : ℝ) ≤ ‖w‖ →
      (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*w).re ≤ 0 →
      (9/5 : ℝ) < (conj ends.v₂*w).re) := by
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR₁ : 0 < ‖ends.P₁‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn ends.deficit_pos₁.le, ends.scaled_deficit₁]
  have hR₂ : 0 < ‖ends.P₂‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn ends.deficit_pos₂.le, ends.scaled_deficit₂]
  have haxis {P : ℂ} (hp : 0 < ‖P‖) : ‖P/(‖P‖ : ℂ)‖=1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_self hp.ne']
  have hd₁ := unit_ray_distance_small _ _ (haxis hR₁) ends.ray₁ hk ends.angle₁
  have hd₂ := unit_ray_distance_small _ _ (haxis hR₂) ends.ray₂ hk ends.angle₂
  constructor
  · intro w hw hr hforward
    exact exteriorOmitted_actualEndpoint_forward_outer_projection F hc k hk ends.P₁ ends.mem₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.scaled_width₁ w hw hr hforward ends.v₁ hd₁
  · intro w hw hr hback
    exact exteriorOmitted_selected_second_outer_projection F hc k hk ends.P₁ ends.P₂
      ends.mem₁ ends.mem₂ ends.deficit_pos₁ ends.scaled_deficit₁ ends.scaled_width₁
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.opposite w hw hr hback ends.v₂ hd₂

end SpringerLean

#print axioms SpringerLean.ActualCandidatePhaseEndpoints.outer_projections
