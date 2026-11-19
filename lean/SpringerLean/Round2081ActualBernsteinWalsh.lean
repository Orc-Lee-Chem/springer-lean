import SpringerLean.Round2070SmoothExteriorBoundaryLaw
import SpringerLean.Round1939FactorConstantDefinitions
import Mathlib.Analysis.Complex.AbsMax

open MeasureTheory Set Metric Filter Polynomial
open scoped Topology

namespace SpringerLean

/-- A continuous function bounded above by `M` on the actual omitted
set is bounded above by `M+ε` on all sufficiently close outer omitted
sets. This uses the nested compact sets of the unscaled outer maps. -/
theorem exteriorOmittedAtScale_eventually_continuous_le
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (f : ℂ → ℝ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ z ∈ exteriorOmitted F, f z ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ z ∈ exteriorOmittedAtScale F (omittedScaleSeq j), f z ≤ M+ε := by
  have hex : ∃ j : ℕ, ∀ z ∈ exteriorOmittedAtScale F (omittedScaleSeq j), f z ≤ M+ε := by
    by_contra! ht
    let T (j : ℕ) := exteriorOmittedAtScale F (omittedScaleSeq j) ∩ {z | M+ε ≤ f z}
    have hclosed : ∀ j : ℕ, IsClosed (T j) := fun j =>
      (exteriorOmittedAtScale_isCompact F hF (omittedScaleSeq_pos j)
        (omittedScaleSeq_lt_one j)).isClosed.inter (isClosed_le continuous_const hf)
    have hT0 : IsCompact (T 0) :=
      (exteriorOmittedAtScale_isCompact F hF (omittedScaleSeq_pos 0)
        (omittedScaleSeq_lt_one 0)).inter_right (isClosed_le continuous_const hf)
    have hnon : ∀ j : ℕ, (T j).Nonempty := by
      intro j
      obtain ⟨z,hz,hlt⟩ := ht j
      exact ⟨z,hz,hlt.le⟩
    have hmono (j : ℕ) : T (j+1) ⊆ T j :=
      inter_subset_inter_left _ (exteriorOmittedAtScale_mono F (omittedScaleSeq_pos j)
        (omittedScaleSeq_mono (Nat.le_succ j)))
    obtain ⟨z,hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      T hmono hnon hT0 hclosed
    have hz0 : M+ε ≤ f z := (mem_iInter.mp hz 0).2
    have hzK : z ∈ exteriorOmitted F := by
      rw [← exteriorOmitted_eq_iInter_scaleSeq F]
      exact mem_iInter.mpr fun j => (mem_iInter.mp hz j).1
    linarith [hM z hzK]
  obtain ⟨j,hj⟩ := hex
  filter_upwards [eventually_ge_atTop j] with i hi z hz
  exact hj z (exteriorOmittedAtScale_mono F (omittedScaleSeq_pos j) (omittedScaleSeq_mono hi) hz)

/-- Bernstein–Walsh for a product of the actual linear factors, in
the capacity-one exterior coordinate. This estimates the product by
its actual norm on the unscaled omitted set. -/
theorem exterior_linear_product_bernsteinWalsh
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hKne : (exteriorOmitted F).Nonempty)
    (n : ℕ) (a : Fin n → ℂ) (w : ℂ) (hw : w ∈ exteriorDisk) :
    ‖(∏ i : Fin n, (X - C (a i) : ℂ[X])).eval (F w)‖ ≤
      continuumPolynomialNorm (exteriorOmitted F) (∏ i : Fin n, (X - C (a i))) * ‖w‖ ^ n := by
  let K := exteriorOmitted F
  let P : ℂ[X] := ∏ i : Fin n, (X - C (a i))
  let M := continuumPolynomialNorm K P
  let G (z : ℂ) := ∏ i : Fin n, exteriorJensenFunction F (a i) z
  have hG : AnalyticOnNhd ℂ G (ball 0 1) := by
    intro z hz
    classical
    have hprod (T : Finset (Fin n)) :
        AnalyticAt ℂ (fun u => ∏ i ∈ T, exteriorJensenFunction F (a i) u) z := by
      induction T using Finset.induction_on with
      | empty => simpa using (analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ)) (x := z))
      | insert i T hi ih =>
        simp_rw [Finset.prod_insert hi]
        exact (exteriorJensenFunction_analytic F hF (a i) z hz).mul ih
    exact hprod _
  have hg (z : ℂ) (hz : z ≠ 0) :
      G z = z^n * P.eval (F z⁻¹) := by
    unfold G P
    simp_rw [exteriorJensenFunction_punctured F _ z hz, eval_prod, eval_sub, eval_X, eval_C,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hK := exteriorOmitted_isCompact F hF
  have hM0 := continuumPolynomialNorm_nonneg K hK hKne P
  obtain ⟨x,hx,hmax⟩ := continuumPolynomialNorm_attained K hK hKne P
  have hbound (y : ℂ) (hy : y ∈ K) : ‖P.eval y‖ ≤ M := by
    dsimp [M]
    rw [continuumPolynomialNorm_eq_at_max K hK hKne P hx hmax]
    exact hmax y hy
  have hw0 := exterior_ne_zero hw
  have hw1 : 1 < ‖w‖ := hw
  have hwinv : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]
    exact (inv_lt_one₀ (norm_pos_iff.mpr hw0)).mpr hw1
  have hGbound : ‖G w⁻¹‖ ≤ M := by
    by_contra! hbad
    let ε := (‖G w⁻¹‖ - M) / 2
    have hε : 0 < ε := half_pos (sub_pos.mpr hbad)
    have hlarge := exteriorOmittedAtScale_eventually_continuous_le F hF
      (fun z => ‖P.eval z‖) P.continuous.norm M hbound ε hε
    obtain ⟨j,hjw,hj⟩ :=
      ((omittedScaleSeq_tendsto_one.eventually (lt_mem_nhds hwinv)).and hlarge).exists
    let s := omittedScaleSeq j
    have hs0 : 0 < s := omittedScaleSeq_pos j
    have hs1 : s < 1 := omittedScaleSeq_lt_one j
    have hDiff : DiffContOnCl ℂ G (ball 0 s) := by
      have hcb : closedBall (0 : ℂ) s ⊆ ball 0 1 := closedBall_subset_ball hs1
      refine ⟨hG.differentiableOn.mono (ball_subset_closedBall.trans hcb), ?_⟩
      rw [closure_ball _ hs0.ne']
      exact hG.continuousOn.mono hcb
    have hfront (z : ℂ) (hz : z ∈ frontier (ball (0 : ℂ) s)) :
        ‖G z‖ ≤ M+ε := by
      rw [frontier_ball _ hs0.ne', mem_sphere, dist_zero_right] at hz
      have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hz.trans_ne hs0.ne')
      have hzE : z⁻¹ ∈ exteriorDisk := by
        change 1 < ‖z⁻¹‖
        rw [norm_inv,hz]
        exact (one_lt_inv₀ hs0).mpr hs1
      have hy : F z⁻¹ ∈ exteriorOmittedAtScale F s := by
        rintro ⟨u,hu,hFu⟩
        have hu' : s⁻¹ < ‖u‖ := hu
        have huE : u ∈ exteriorDisk := ((one_lt_inv₀ hs0).mpr hs1).trans hu'
        rw [hF.2.1 huE hzE hFu,norm_inv,hz] at hu'
        exact lt_irrefl _ hu'
      rw [hg z hz0, norm_mul, norm_pow, hz]
      have hsN : s^n ≤ 1 := pow_le_one₀ hs0.le hs1.le
      exact ((mul_le_mul_of_nonneg_right hsN (norm_nonneg _)).trans
        (by simpa only [one_mul] using hj _ hy))
    have hmem : w⁻¹ ∈ closure (ball (0 : ℂ) s) :=
      subset_closure (by simpa [mem_ball, dist_zero_right] using hjw)
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le
      isBounded_ball hDiff hfront hmem
    dsimp [ε] at hle
    linarith
  change ‖P.eval (F w)‖ ≤ M * ‖w‖^n
  rw [hg _ (inv_ne_zero hw0), inv_inv, norm_mul, norm_pow, norm_inv,
    inv_pow, ← div_eq_inv_mul] at hGbound
  exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hw0) n)).mp hGbound

end SpringerLean
