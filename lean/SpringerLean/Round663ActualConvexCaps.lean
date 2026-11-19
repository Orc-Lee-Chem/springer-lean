import SpringerLean.Round659OmittedRadiusCoefficient
import SpringerLean.Round645ActualBoundaryConvex

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean
set_option Elab.async false

theorem rescaleExterior_inverseCoeff_mul_norm_tendsto_scaleSeq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto
      (fun j : ℕ => (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior (omittedScaleSeq j) F) n‖)
      atTop (𝓝 ((n : ℝ)*‖exteriorInverseCoeff F n‖)) := by
  have hfun :
      (fun j : ℕ => (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior (omittedScaleSeq j) F) n‖) =
      (fun j : ℕ => (n : ℝ)*(omittedScaleSeq j^(n+1)*‖exteriorInverseCoeff F n‖)) := by
    funext j
    rw [rescaleExterior_inverseCoeff F hc (omittedScaleSeq_pos j)
      (omittedScaleSeq_lt_one j) hn,norm_mul,norm_pow]
    have hsN : ‖(omittedScaleSeq j : ℂ)‖=omittedScaleSeq j := by
      simp [abs_of_pos (omittedScaleSeq_pos j)]
    rw [hsN]
  rw [hfun]
  have h := (tendsto_const_nhds (x := (n : ℝ))).mul
    ((omittedScaleSeq_tendsto_one.pow (n+1)).mul
      (tendsto_const_nhds (x := ‖exteriorInverseCoeff F n‖)))
  simpa only [one_pow,one_mul] using h

/-- An actual omitted-set cap can use finitely many directions, fixed
after F is given. The geometric cap hypothesis is explicit and must be
proved in any application; all regularized/trace/integral hypotheses have
been discharged. This is not yet an all-k Catalan theorem. -/
theorem exteriorInverseCoeff_mul_norm_le_of_finite_convex_caps
    {ι : Type*} (S : Finset ι)
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n) (ξ : ι → ℂ)
    (hξ : ∀ i ∈ S, ‖ξ i‖=1) (ψ : ι → ℝ → ℝ)
    (hψ : ∀ i ∈ S, ConvexOn ℝ Set.univ (ψ i)) (c : ℝ)
    (hcap : ∀ w ∈ exteriorOmitted F,
      ‖w‖^n ≤ c+∑ i ∈ S, ψ i ((conj (ξ i)*w).re)) :
    (n : ℝ)*‖exteriorInverseCoeff F n‖ ≤
      c+∑ i ∈ S, Real.circleAverage (fun ζ : ℂ => ψ i (2*ζ.re)) 0 1 := by
  classical
  have hψc (i : ι) (hi : i ∈ S) : Continuous (ψ i) := by
    simpa only [continuousOn_univ] using (ConvexOn.continuousOn isOpen_univ (hψ i hi))
  let J : ℂ → ℝ := fun w => c+∑ i ∈ S, ψ i ((conj (ξ i)*w).re)
  have hJc : Continuous J := by
    apply continuous_const.add
    exact continuous_finsetSum S (fun i hi => (hψc i hi).comp (by fun_prop))
  apply le_of_forall_pos_le_add
  intro ε hε
  have hclose := exteriorOmitted_rescale_inequality_eventually_scaleSeq F hc
    Set.univ isClosed_univ (fun w => ‖w‖^n-J w)
    ((continuous_norm.pow n).sub hJc)
    (fun w hw _ => sub_nonpos.mpr (hcap w hw)) hε
  have hbound : ∀ᶠ j : ℕ in atTop,
      (n : ℝ)*‖exteriorInverseCoeff (rescaleExterior (omittedScaleSeq j) F) n‖ ≤
        (c+∑ i ∈ S, Real.circleAverage (fun ζ : ℂ => ψ i (2*ζ.re)) 0 1)+ε := by
    filter_upwards [hclose] with j hj
    let s := omittedScaleSeq j
    have hs0 : 0 < s := omittedScaleSeq_pos j
    have hs1 : s < 1 := omittedScaleSeq_lt_one j
    have hIi (i : ι) (hi : i ∈ S) : CircleIntegrable
        (fun ζ => ψ i ((conj (ξ i)*rescaleExterior s F ζ).re)) 0 1 :=
      ((hψc i hi).comp_continuousOn
        (regularExterior_projection_continuousOn_sphere F hc hs0 hs1 (ξ i))).circleIntegrable
          (by norm_num)
    have hIsum : CircleIntegrable
        (fun ζ => ∑ i ∈ S, ψ i ((conj (ξ i)*rescaleExterior s F ζ).re)) 0 1 := by
      have h := CircleIntegrable.sum S hIi
      convert h using 1
      funext ζ
      simp only [Finset.sum_apply]
    have hIJ : CircleIntegrable (fun ζ => J (rescaleExterior s F ζ)) 0 1 :=
      (circleIntegrable_const _ _ _).add hIsum
    have hshape : Real.circleAverage (fun ζ => J (rescaleExterior s F ζ)) 0 1 =
        c+∑ i ∈ S, Real.circleAverage
          (fun ζ => ψ i ((conj (ξ i)*rescaleExterior s F ζ).re)) 0 1 := by
      change Real.circleAverage (fun ζ => c+∑ i ∈ S,
        ψ i ((conj (ξ i)*rescaleExterior s F ζ).re)) 0 1 = _
      rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hIsum,
        Real.circleAverage_const,Real.circleAverage_fun_sum]
      exact hIi
    have hmodel : Real.circleAverage (fun ζ => J (rescaleExterior s F ζ)) 0 1 ≤
        c+∑ i ∈ S, Real.circleAverage (fun ζ : ℂ => ψ i (2*ζ.re)) 0 1 := by
      rw [hshape]
      exact add_le_add le_rfl (Finset.sum_le_sum (fun i hi =>
        regularExterior_convex_boundary_le F hc hs0 hs1 (ξ i) (hξ i hi) (ψ i) (hψ i hi)))
    have hmoment : Real.circleAverage (fun ζ => ‖rescaleExterior s F ζ‖^n) 0 1 ≤
        Real.circleAverage (fun ζ => J (rescaleExterior s F ζ)+ε) 0 1 := by
      apply Real.circleAverage_mono
        (rescaleExterior_boundary_power_circleIntegrable F hc hs0 hs1 n)
        (hIJ.add (circleIntegrable_const _ _ _))
      intro ζ hζ
      have hζn : ‖ζ‖=1 := by
        simpa only [abs_one,Metric.mem_sphere,dist_zero_right] using hζ
      have hK := rescaleExterior_unitCircle_mem_omitted F hc hs0 hs1 hζn
      have h := hj _ hK (Set.mem_univ _)
      change ‖rescaleExterior s F ζ‖^n ≤ J (rescaleExterior s F ζ)+ε
      linarith
    rw [Real.circleAverage_fun_add hIJ (circleIntegrable_const _ _ _),
      Real.circleAverage_const] at hmoment
    exact ((rescaleExterior_inverseCoeff_mul_norm_le_boundary_moment F hc hs0 hs1 n hn).trans
      hmoment).trans (add_le_add hmodel le_rfl)
  exact le_of_tendsto (rescaleExterior_inverseCoeff_mul_norm_tendsto_scaleSeq F hc n hn) hbound

end SpringerLean
