import SpringerLean.Round2090FiniteFarthestApproximation

open MeasureTheory Polynomial Set Real
open scoped BigOperators

namespace SpringerLean

/-- Farthest distances yield an admissible factor constant on an actual
normalized exterior omitted set. -/
theorem factorInequality_actual_farthest_exp
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (huv : u ≠ v) :
    FactorInequality (exteriorOmitted F) (Real.exp
      (∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
        ∂actualExteriorBoundaryProbability F)) := by
  let K := exteriorOmitted F
  let d := continuumFarthestDistance K
  let μ := actualExteriorBoundaryProbability F
  let J := ∫ z, log (d z) ∂μ
  have hK := exteriorOmitted_isCompact F hF
  have hnK : K.Nonempty := ⟨u,hu⟩
  have hd := continuumFarthestDistance_pos_of_two_points K hK u v hu hv huv
  have hμ : K ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hcompactIntegrable (f : ℂ → ℝ) (hf : Continuous f) : Integrable f μ := by
    obtain ⟨C,hC⟩ := (hK.image hf).isBounded.exists_norm_le
    apply Integrable.mono (integrable_const (max C 0)) hf.aestronglyMeasurable
    filter_upwards [hμ] with z hz
    rw [Real.norm_of_nonneg (le_max_right C 0)]
    exact (hC _ ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hlogI : Integrable (fun z => log (d z)) μ :=
    hcompactIntegrable _ ((continuumFarthestDistance_continuous K hK hnK).log (fun z => (hd z).ne'))
  apply FactorInequality_of_linear_families K hK hnK
  intro n a
  let P : ℂ[X] := ∏ l : Fin n, (X-C (a l))
  let M := continuumPolynomialNorm K P
  have hM : 0 < M := exterior_linear_product_norm_pos F hF n a
  have hlog : (∑ l : Fin n, log (d (a l))) ≤ log M + (n:ℝ)*J := by
    by_contra! hbad
    let gap := (∑ l : Fin n, log (d (a l))) - (log M + (n:ℝ)*J)
    let ε := gap / (2*((n:ℝ)+1))
    have hgap : 0 < gap := sub_pos.mpr hbad
    have hε : 0 < ε := div_pos hgap (by positivity)
    obtain ⟨N,B,i,j,m,hij,hm,happrox⟩ :=
      exists_finiteGaussianLogScale_approximation K hK u v hu hv huv ε hε
    let H := finiteGaussianLogScale B m
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
    have hcont : Continuous H := finiteGaussianLogScale_continuous B i j hij m
    have hb : (∫ z, H z ∂μ) ≤ (m:ℝ)*(J+ε) := by
      calc
        _ ≤ ∫ z, (m:ℝ)*(log (d z)+ε) ∂μ :=
          integral_mono (hcompactIntegrable H hcont)
            ((hlogI.add (integrable_const ε)).const_mul _) (fun z => (happrox z).2)
        _ = _ := by
          rw [integral_const_mul, integral_add hlogI (integrable_const ε),
            integral_const, probReal_univ, one_smul]
    have ha : (m:ℝ)*((∑ l : Fin n, log (d (a l)))-(n:ℝ)*ε) ≤
        ∑ l : Fin n, H (a l) := by
      have hs : (∑ _ : Fin n, ε) = (n:ℝ)*ε := by simp
      rw [← hs, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum (fun l _ => (happrox (a l)).1)
    have hc := linear_product_log_bound_gaussian_average F hF hnK n a N B i j hij m
    change (∑ l : Fin n, H (a l)) ≤ (m:ℝ)*log M + (n:ℝ)*∫ z, H z ∂μ at hc
    have hh := ha.trans (hc.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n))))
    have ht : gap ≤ 2*(n:ℝ)*ε := by
      have hh' : (∑ l : Fin n, log (d (a l)))-(n:ℝ)*ε ≤ log M + (n:ℝ)*(J+ε) := by
        apply le_of_mul_le_mul_left ?_ hmR
        nlinarith only [hh]
      dsimp [gap]
      linarith only [hh']
    have heq : ε * (2*((n:ℝ)+1)) = gap :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith only [ht,heq,hε]
  have hExp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sum, Real.exp_add, Real.exp_log hM, Real.exp_nat_mul, mul_comm M] at hExp
  have heval (z : ℂ) : Real.exp (log (d z)) = d z := Real.exp_log (hd z)
  simpa only [heval] using hExp

/-- The exact least constant in the actual finite-polynomial factor
inequality on the omitted set of a normalized centered exterior map. -/
theorem factorConstant_eq_actual_farthest_exp
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (huv : u ≠ v) :
    factorConstant (exteriorOmitted F) = Real.exp
      (∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
        ∂actualExteriorBoundaryProbability F) := by
  let K := exteriorOmitted F
  let J := ∫ z, log (continuumFarthestDistance K z) ∂actualExteriorBoundaryProbability F
  let A := {c : ℝ | 0 ≤ c ∧ FactorInequality K c}
  have hA : exp J ∈ A := ⟨(exp_pos _).le,factorInequality_actual_farthest_exp F hF u v hu hv huv⟩
  have hbound : BddBelow A := ⟨0, fun _ hc => hc.1⟩
  change sInf A = exp J
  apply le_antisymm (csInf_le hbound hA)
  apply le_csInf ⟨exp J,hA⟩
  intro c hc
  have hd := continuumFarthestDistance_pos_of_two_points K (exteriorOmitted_isCompact F hF)
    u v hu hv huv u
  have hlin := FactorInequality_linear_family K c hc.2 1 (fun _ => u)
  rw [Fin.prod_univ_one, Fin.prod_univ_one, ← continuumFarthestDistance_eq_linear_norm,
    pow_one] at hlin
  have h1 : 1 ≤ c := le_of_mul_le_mul_right (by simpa only [one_mul] using hlin) hd
  have hlog : J ≤ log c := factorInequality_log_ge_actual_farthest F hF u v hu hv huv c hc.2
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (zero_lt_one.trans_le h1))

end SpringerLean
