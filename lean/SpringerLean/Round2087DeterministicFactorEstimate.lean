import SpringerLean.Round2084FactorUpperPotentialReduction

open MeasureTheory Set Filter Polynomial
open scoped BigOperators

namespace SpringerLean

private theorem exteriorRadial_kernel_integrable_ne
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (a : ℂ) :
    (∀ᵐ x ∂actualExteriorBoundaryProbability F, x ≠ a) ∧
      Integrable (fun x => Real.log ‖x-a‖) (actualExteriorBoundaryProbability F) := by
  let K := exteriorOmitted F
  let μ := actualExteriorBoundaryProbability F
  by_cases ha : a ∈ K
  · exact (actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF a ha).imp
      id fun h => h.1
  · have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
    have hK := exteriorOmitted_isCompact F hF
    have hμ : K ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
    refine ⟨?_,?_⟩
    · filter_upwards [hμ] with x hx
      exact fun he => ha (he ▸ hx)
    · have hc : ContinuousOn (fun x => Real.log ‖x-a‖) K :=
        ((continuous_id.sub continuous_const).norm.continuousOn).log (fun x hx =>
          norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => ha ((show x = a from he) ▸ hx))))
      obtain ⟨M,hM⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
      apply Integrable.mono (integrable_const (max M 0))
        (Real.measurable_log.comp ((continuous_id.sub continuous_const).norm.measurable)).aestronglyMeasurable
      filter_upwards [hμ] with x hx
      rw [Real.norm_of_nonneg (le_max_right M 0)]
      exact (hM _ ⟨x,hx,rfl⟩).trans (le_max_left _ _)

private theorem norm_prod_map_complex (A : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(A.map f).prod‖ = (A.map (fun x => ‖f x‖)).prod := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih => simp [norm_mul, ih]

private theorem polynomial_log_eval_sum_roots (Q : ℂ[X]) (hQ : Q ≠ 0)
    (x : ℂ) (hx : Q.eval x ≠ 0) :
    Real.log ‖Q.eval x‖ = Real.log ‖Q.leadingCoeff‖ +
      (Q.roots.map (fun a => Real.log ‖x-a‖)).sum := by
  have hc := (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm
  have hpoly := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hval := congrArg (fun P : ℂ[X] => P.eval x) hpoly
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    eval_sub, eval_X] at hval
  have hnonzero : ∀ a ∈ Q.roots, ‖x-a‖ ≠ 0 := by
    intro a ha
    apply norm_ne_zero_iff.mpr
    intro he
    exact hx ((sub_eq_zero.mp he).symm ▸ (mem_roots hQ).mp ha)
  have hprod : (Q.roots.map (fun a => ‖x-a‖)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨a,ha,he⟩ := Multiset.mem_map.mp h0
    exact hnonzero a ha he
  rw [← hval, norm_mul, norm_prod_map_complex,
    Real.log_mul (norm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr hQ)) hprod,
    Real.log_multiset_prod]
  · simp only [Multiset.map_map, Function.comp_apply]
  · intro y hy
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hy
    exact hnonzero a ha

/-- Logarithmic integration of a polynomial against the actual radial
law gives the sum of Green coordinates of its roots with multiplicity. -/
theorem actualRadialProbability_integral_log_polynomial
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (Q : ℂ[X]) (hQ : Q ≠ 0) :
    Integrable (fun z => Real.log ‖Q.eval z‖) (actualExteriorBoundaryProbability F) ∧
      (∫ z, Real.log ‖Q.eval z‖ ∂actualExteriorBoundaryProbability F) =
        Real.log ‖Q.leadingCoeff‖ + (Q.roots.map (exteriorGreenCoordinate F)).sum := by
  let μ := actualExteriorBoundaryProbability F
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  let g (a z : ℂ) := Real.log ‖z-a‖
  have hroot (A : Multiset ℂ) : ∀ᵐ z ∂μ, ∀ a ∈ A, z ≠ a := by
    induction A using Multiset.induction_on with
    | empty => exact .of_forall (by simp)
    | cons a A ih =>
      filter_upwards [(exteriorRadial_kernel_integrable_ne F hF a).1, ih] with z hz hA
      intro b hb
      rcases Multiset.mem_cons.mp hb with rfl | hb
      · exact hz
      · exact hA _ hb
  have heq : (fun z => Real.log ‖Q.eval z‖) =ᵐ[μ]
      fun z => Real.log ‖Q.leadingCoeff‖ + (Q.roots.map (fun a => g a z)).sum := by
    filter_upwards [hroot Q.roots] with z hz
    exact polynomial_log_eval_sum_roots Q hQ z (fun h =>
      hz z ((mem_roots hQ).mpr h) rfl)
  have hsum (A : Multiset ℂ) :
      Integrable (fun z => (A.map (fun a => g a z)).sum) μ ∧
        (∫ z, (A.map (fun a => g a z)).sum ∂μ) = (A.map (exteriorGreenCoordinate F)).sum := by
    induction A using Multiset.induction_on with
    | empty => simp
    | cons a A ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      have ha : Integrable (g a) μ := (exteriorRadial_kernel_integrable_ne F hF a).2
      exact ⟨ha.add ih.1, by
        rw [integral_add ha ih.1, ih.2, exteriorGreenCoordinate_eq_radial_potential F hF a]⟩
  have hi := (integrable_const (Real.log ‖Q.leadingCoeff‖)).add (hsum Q.roots).1
  refine ⟨hi.congr heq.symm,?_⟩
  rw [integral_congr_ae heq, integral_add (integrable_const _) (hsum Q.roots).1,
    integral_const, probReal_univ, one_smul, (hsum Q.roots).2]

/-- For a fixed auxiliary polynomial this is the complete deterministic
inequality used before averaging over Gaussian coefficients. The
leading-coefficient contributions cancel by finite factorization. -/
theorem auxiliary_polynomial_linear_product_log_bound
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hK : (exteriorOmitted F).Nonempty)
    (n : ℕ) (a : Fin n → ℂ) (P : ℂ[X])
    (hP : P = ∏ i : Fin n, (X-C (a i))) (hM : 0 < continuumPolynomialNorm (exteriorOmitted F) P)
    (Q : ℂ[X]) (hQ : Q ≠ 0) (hQa : ∀ i : Fin n, Q.eval (a i) ≠ 0) :
    (∑ i : Fin n, Real.log ‖Q.eval (a i)‖) ≤
      (Q.natDegree:ℝ) * Real.log (continuumPolynomialNorm (exteriorOmitted F) P) +
        (n:ℝ) * ∫ z, Real.log ‖Q.eval z‖ ∂actualExteriorBoundaryProbability F := by
  let K := exteriorOmitted F
  let M := continuumPolynomialNorm K P
  let G := exteriorGreenCoordinate F
  have hc := (IsAlgClosed.splits Q).natDegree_eq_card_roots.symm
  have hprod (x : ℂ) : ‖P.eval x‖ = ∏ i : Fin n, ‖x-a i‖ := by
    simp [hP, eval_prod, eval_sub, norm_prod]
  have hpos (x : ℂ) (hx : x ∈ Q.roots) : 0 < ‖P.eval x‖ := by
    rw [hprod]
    apply Finset.prod_pos
    intro i _
    apply norm_pos_iff.mpr
    intro he
    exact hQa i ((sub_eq_zero.mp he) ▸ (mem_roots hQ).mp hx)
  have hpw (x : ℂ) (hx : x ∈ Q.roots) :
      Real.log ‖P.eval x‖ ≤ Real.log M + (n:ℝ)*G x := by
    by_cases hxE : x ∈ F '' exteriorDisk
    · obtain ⟨w,hw,rfl⟩ := hxE
      have hmem : F w ∈ F '' exteriorDisk := ⟨w,hw,rfl⟩
      have h := exterior_linear_product_bernsteinWalsh F hF hK n a w hw
      rw [← hP] at h
      have hl := Real.log_le_log (hpos _ hx) h
      change Real.log ‖P.eval (F w)‖ ≤ Real.log (M*‖w‖^n) at hl
      rw [Real.log_mul hM.ne' (pow_ne_zero _ (norm_ne_zero_iff.mpr (exterior_ne_zero hw))),
        Real.log_pow] at hl
      simpa only [G, exteriorGreenCoordinate, if_pos hmem, exteriorInverse,
        hF.2.1.leftInvOn_invFunOn hw] using hl
    · have hcompact := exteriorOmitted_isCompact F hF
      obtain ⟨z,hz,hmax⟩ := continuumPolynomialNorm_attained K hcompact hK P
      have hnorm : ‖P.eval x‖ ≤ M := by
        dsimp only [M]
        rw [continuumPolynomialNorm_eq_at_max K hcompact hK P hz hmax]
        exact hmax x hxE
      simpa only [G, exteriorGreenCoordinate, if_neg hxE, mul_zero, add_zero] using
        Real.log_le_log (hpos _ hx) hnorm
  have hsum (A : Multiset ℂ) (hA : ∀ x ∈ A, x ∈ Q.roots) :
      (A.map (fun x => Real.log ‖P.eval x‖)).sum ≤
        (A.card:ℝ)*Real.log M + (n:ℝ)*(A.map G).sum := by
    induction A using Multiset.induction_on with
    | empty => simp
    | cons x A ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one]
      have hx := hpw x (hA x (Multiset.mem_cons_self _ _))
      have hrem := ih (fun r hr => hA r (Multiset.mem_cons_of_mem hr))
      linarith
  have hrootComm (A : Multiset ℂ) :
      (∑ i : Fin n, (A.map (fun x => Real.log ‖a i-x‖)).sum) =
        (A.map (fun x => ∑ i : Fin n, Real.log ‖x-a i‖)).sum := by
    induction A using Multiset.induction_on with
    | empty => simp
    | cons x A ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sub_rev]
  have hex (x : ℂ) (hx : x ∈ Q.roots) :
      (∑ i : Fin n, Real.log ‖x-a i‖) = Real.log ‖P.eval x‖ := by
    have hn (i : Fin n) : ‖x-a i‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      apply sub_ne_zero.mpr
      intro he
      have hr : Q.eval x = 0 := (mem_roots hQ).mp hx
      exact hQa i (by rw [← he]; exact hr)
    rw [hprod, Real.log_prod (fun i _ => hn i)]
  have hmaps : Q.roots.map (fun x => ∑ i : Fin n, Real.log ‖x-a i‖) =
      Q.roots.map (fun x => Real.log ‖P.eval x‖) := Multiset.map_congr rfl hex
  have hfinal := hsum Q.roots (fun _ h => h)
  rw [hc] at hfinal
  have hf (i : Fin n) := polynomial_log_eval_sum_roots Q hQ (a i) (hQa i)
  simp_rw [hf]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hrootComm, hmaps,
    (actualRadialProbability_integral_log_polynomial F hF Q hQ).2]
  change _ ≤ (Q.natDegree:ℝ) * Real.log M + _
  linarith

end SpringerLean
