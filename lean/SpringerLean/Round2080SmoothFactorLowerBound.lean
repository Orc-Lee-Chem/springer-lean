import SpringerLean.Round2070SmoothExteriorBoundaryLaw
import SpringerLean.Round2079UniformAngularSampling
import SpringerLean.Round2014OddStarFarthestIntegral

open MeasureTheory Set Real Polynomial
open scoped BigOperators

namespace SpringerLean

/-- A nondegenerate compact set has a strictly positive farthest
distance everywhere. -/
theorem continuumFarthestDistance_pos_of_two_points (K : Set ℂ) (hK : IsCompact K)
    (u v : ℂ) (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v) (z : ℂ) :
    0 < continuumFarthestDistance K z := by
  by_cases hz : z = u
  · exact (norm_pos_iff.mpr (sub_ne_zero.mpr (hz.trans_ne hne))).trans_le
      (continuumFarthestDistance_ge_distance K hK z v hv)
  · exact (norm_pos_iff.mpr (sub_ne_zero.mpr hz)).trans_le
      (continuumFarthestDistance_ge_distance K hK z u hu)

/-- Every admissible factor constant dominates the smooth outer-circle
farthest-distance mean divided by the radius.  The lower bound uses
only actual linear factors, uniformly sampled from that circle. -/
theorem factorInequality_log_ge_smooth_farthest
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (hne : u ≠ v)
    (c : ℝ) (hc : FactorInequality (exteriorOmitted F) c)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
      ∂smoothExteriorBoundaryProbability F s) + Real.log s ≤ Real.log c := by
  let K := exteriorOmitted F
  have hK := exteriorOmitted_isCompact F hF
  have hKne : K.Nonempty := ⟨u,hu⟩
  let d := continuumFarthestDistance K
  have hd (z : ℂ) : 0 < d z :=
    continuumFarthestDistance_pos_of_two_points K hK u v hu hv hne z
  let g (θ : ℝ) := F (circleMap 0 s⁻¹ θ)
  have hse : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  have hmem (θ : ℝ) : circleMap 0 s⁻¹ θ ∈ exteriorDisk := by
    change 1 < ‖circleMap 0 s⁻¹ θ‖
    simpa only [norm_circleMap_zero, abs_of_pos (inv_pos.mpr hs0)] using hse
  have hg : Continuous g :=
    hF.1.continuousOn.comp_continuous (continuous_circleMap _ _) hmem
  have hdist (θ : ℝ) (x : ℂ) (hx : x ∈ K) : ‖g θ - x‖ ≠ 0 := by
    intro heq
    exact hx ⟨_, hmem θ, sub_eq_zero.mp (norm_eq_zero.mp heq)⟩
  have hdc : Continuous (fun z => Real.log (d z)) :=
    (continuumFarthestDistance_continuous K hK hKne).log (fun z => (hd z).ne')
  let H (p : ℂ × ℝ) := Real.log (d (g p.2)) - Real.log ‖g p.2 - p.1‖
  have hH : ContinuousOn H (K ×ˢ Icc 0 (2*π)) := by
    apply (hdc.comp (hg.comp continuous_snd)).continuousOn.sub
    apply (((hg.comp continuous_snd).sub continuous_fst).norm.continuousOn).log
    exact fun p hp => hdist p.2 p.1 hp.1
  let J := ∫ z, Real.log (d z) ∂smoothExteriorBoundaryProbability F s
  have hJ : J = circleAverage (fun w => Real.log (d (F w))) 0 s⁻¹ :=
    smoothExteriorBoundaryProbability_integral_eq_circleAverage F hF s hs0 hs1
      _ hdc.measurable
  by_contra! hbad
  let ε : ℝ := (J + Real.log s - Real.log c)/2
  have hε : 0 < ε := half_pos (sub_pos.mpr hbad)
  obtain ⟨n,hn,happrox⟩ :=
    exists_uniform_interval_samples K hK 0 (2*π) Real.two_pi_pos H hH ε hε
  let a (i : Fin n) := g (2*π/(n:ℝ)*(i:ℝ))
  let P : ℂ[X] := ∏ i : Fin n, (X - C (a i))
  obtain ⟨x,hx,hmax⟩ := continuumPolynomialNorm_attained K hK hKne P
  have hprod : continuumPolynomialNorm K P = ∏ i : Fin n, ‖a i - x‖ := by
    rw [continuumPolynomialNorm_eq_at_max K hK hKne P hx hmax]
    simp [P, eval_prod, eval_sub, norm_prod, norm_sub_rev]
  have hp : 0 < continuumPolynomialNorm K P := by
    rw [hprod]
    exact Finset.prod_pos (fun i _ => lt_of_le_of_ne (norm_nonneg _)
      (hdist _ x hx).symm)
  have hcle : 0 < c := by
    have hlin := FactorInequality_linear_family K c hc 1 (fun _ => u)
    have heq : (∏ i : Fin 1, (X - C ((fun _ : Fin 1 => u) i) : ℂ[X])) = X-C u := by simp
    rw [heq, ← continuumFarthestDistance_eq_linear_norm, pow_one] at hlin
    have h1 : 1 ≤ c := by
      simp only [Fin.prod_univ_one] at hlin
      exact le_of_mul_le_mul_right (by simpa only [one_mul] using hlin) (hd u)
    exact zero_lt_one.trans_le h1
  have hconst := FactorInequality_linear_family K c hc n a
  have hlog := Real.log_le_log (Finset.prod_pos (fun i _ => hd (a i))) hconst
  change Real.log (∏ i : Fin n, d (a i)) ≤
    Real.log (c ^ n * continuumPolynomialNorm K P) at hlog
  rw [Real.log_mul (pow_ne_zero _ hcle.ne') hp.ne', Real.log_pow, hprod,
    Real.log_prod (fun i _ => (hd (a i)).ne'),
    Real.log_prod (fun i _ => hdist _ x hx)] at hlog
  have hsum : (∑ i ∈ Finset.range n, H (x, (2*π)/(n:ℝ)*i)) ≤ (n:ℝ)*Real.log c := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [H, a, Finset.sum_sub_distrib]
    linarith
  have hi1 : IntervalIntegrable (fun θ => Real.log (d (g θ))) volume 0 (2*π) :=
    (hdc.comp hg).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => Real.log ‖g θ-x‖) volume 0 (2*π) :=
    (((hg.sub continuous_const).norm).log (fun θ => hdist θ x hx)).intervalIntegrable _ _
  have hmean : (∫ θ in 0..2*π, H (x,θ)) = (2*π)*(J + Real.log s) := by
    have heq := exterior_circle_log_potential_of_omitted F hF x hx s hs0 hs1
    rw [hJ, circleAverage_def, smul_eq_mul]
    rw [circleAverage_def, smul_eq_mul] at heq
    dsimp [H]
    rw [intervalIntegral.integral_sub hi1 hi2]
    dsimp [g]
    have hh : (2*π) * (2*π)⁻¹ = 1 := mul_inv_cancel₀ Real.two_pi_pos.ne'
    have heq' := congrArg (fun w : ℝ => (2*π)*w) heq
    simp only [← mul_assoc, hh, one_mul] at heq'
    rw [mul_add, ← mul_assoc, hh, one_mul]
    linarith
  have herror := happrox x hx
  rw [hmean] at herror
  simp only [sub_zero, zero_add] at herror
  have hdiff := (abs_le.mp herror).2
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hbound := mul_le_mul_of_nonneg_left hsum (div_nonneg Real.two_pi_pos.le hnR.le)
  have hden : (2*π / (n:ℝ)) * ((n:ℝ)*Real.log c) = (2*π)*Real.log c := by
    field_simp
  rw [hden] at hbound
  dsimp [ε] at hdiff
  have hb : 0 < (2*π)*(J + Real.log s - Real.log c) :=
    mul_pos Real.two_pi_pos (sub_pos.mpr hbad)
  nlinarith

end SpringerLean
