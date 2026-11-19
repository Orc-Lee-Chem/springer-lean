import SpringerLean.Round2075ExteriorMutualEnergy
import SpringerLean.Round2081ActualBernsteinWalsh
import SpringerLean.Round2082ActualFactorLowerBound
import SpringerLean.Round2083FactorRootFamilies

open MeasureTheory Set Filter Polynomial Real
open scoped BigOperators

namespace SpringerLean

/-- Green coordinate on the actual exterior image, extended by zero
on the omitted set. -/
noncomputable def exteriorGreenCoordinate (F : ℂ → ℂ) (x : ℂ) : ℝ := by
  classical
  exact if x ∈ F '' exteriorDisk then Real.log ‖exteriorInverse F x‖ else 0

theorem exteriorGreenCoordinate_eq_radial_potential
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ) :
    exteriorGreenCoordinate F x =
      ∫ z, Real.log ‖z-x‖ ∂actualExteriorBoundaryProbability F := by
  by_cases hx : x ∈ F '' exteriorDisk
  · have hw : exteriorInverse F x ∈ exteriorDisk := Function.invFunOn_mem hx
    have hval : F (exteriorInverse F x) = x := Function.invFunOn_eq hx
    unfold exteriorGreenCoordinate
    rw [if_pos hx, ← actualExteriorBoundaryProbability_log_potential_at_image F hF _ hw, hval]
  · rw [exteriorGreenCoordinate, if_neg hx,
      actualExteriorBoundaryProbability_log_potential_on_omitted F hF x hx]

theorem exterior_linear_product_norm_pos
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (n : ℕ) (a : Fin n → ℂ) :
    0 < continuumPolynomialNorm (exteriorOmitted F)
      (∏ i : Fin n, (X-C (a i))) := by
  let μ := actualExteriorBoundaryProbability F
  let K := exteriorOmitted F
  let P : ℂ[X] := ∏ i : Fin n, (X-C (a i))
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hK := exteriorOmitted_isCompact F hF
  have hμ : K ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
  have havoid (i : Fin n) : ∀ᵐ z ∂μ, z ≠ a i := by
    by_cases hi : a i ∈ K
    · exact (actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF _ hi).1
    · filter_upwards [hμ] with z hz
      exact fun heq => hi (heq ▸ hz)
  obtain ⟨x, hx, hne⟩ := ((show ∀ᵐ z ∂μ, z ∈ K from hμ).and (ae_all_iff.mpr havoid)).exists
  obtain ⟨y,hy,hmax⟩ := continuumPolynomialNorm_attained K hK ⟨x,hx⟩ P
  have hPx : 0 < ‖P.eval x‖ := by
    dsimp only [P]
    simp only [eval_prod, eval_sub, eval_X, eval_C, norm_prod]
    exact Finset.prod_pos (fun i _ => norm_pos_iff.mpr (sub_ne_zero.mpr (hne i)))
  change 0 < continuumPolynomialNorm K P
  rw [continuumPolynomialNorm_eq_at_max K hK ⟨x,hx⟩ P hy hmax]
  exact hPx.trans_le (hmax x hx)

/-- A probability whose logarithmic potential approximates the
farthest-distance logarithm from below gives an admissible constant.
The mixed integrability premise allows measures with unbounded
support. A separate construction must supply such a probability. -/
theorem factorInequality_of_farthest_log_potential_approximation
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (u v : ℂ) (hu : u ∈ exteriorOmitted F) (hv : v ∈ exteriorOmitted F) (hne : u ≠ v)
    (ε : ℝ) (σ : Measure ℂ) [IsProbabilityMeasure σ]
    (hσ : ∀ x : ℂ, (∀ᵐ z ∂σ, z ≠ x) ∧ Integrable (fun z => Real.log ‖z-x‖) σ ∧
      (∫ z, Real.log ‖z-x‖ ∂σ) ≤ Real.log (continuumFarthestDistance (exteriorOmitted F) x) ∧
      Real.log (continuumFarthestDistance (exteriorOmitted F) x) ≤
        (∫ z, Real.log ‖z-x‖ ∂σ) + ε)
    (hmixed : Integrable (fun p : ℂ × ℂ => Real.log ‖p.2-p.1‖)
      (σ.prod (actualExteriorBoundaryProbability F))) :
    FactorInequality (exteriorOmitted F)
      (Real.exp ((∫ z, Real.log (continuumFarthestDistance (exteriorOmitted F) z)
        ∂actualExteriorBoundaryProbability F) + ε)) := by
  let K := exteriorOmitted F
  let μ := actualExteriorBoundaryProbability F
  let d := continuumFarthestDistance K
  let U (x : ℂ) := ∫ z, Real.log ‖z-x‖ ∂σ
  let J := ∫ z, Real.log (d z) ∂μ
  let G := exteriorGreenCoordinate F
  let C0 := Real.exp (J + ε)
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hK := exteriorOmitted_isCompact F hF
  have hc : K.Nonempty := ⟨u,hu⟩
  have hd (z : ℂ) : 0 < d z :=
    continuumFarthestDistance_pos_of_two_points K hK u v hu hv hne z
  have hGσ : Integrable G σ := by
    unfold G
    rw [funext (exteriorGreenCoordinate_eq_radial_potential F hF)]
    exact hmixed.integral_prod_left
  have hUμ : Integrable U μ := by
    unfold U
    have hi : Integrable (fun y => ∫ x, Real.log ‖y-x‖ ∂σ) μ :=
      hmixed.integral_prod_right
    simpa only [norm_sub_rev] using hi
  have hdμ : Integrable (fun z => Real.log (d z)) μ := by
    have hcont : Continuous (fun z => Real.log (d z)) :=
      (continuumFarthestDistance_continuous K hK hc).log (fun z => (hd z).ne')
    have hmem : K ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted F hF hK.isClosed
    obtain ⟨M,hM⟩ := (hK.image hcont).isBounded.exists_norm_le
    apply Integrable.mono (integrable_const (max M 0)) hcont.aestronglyMeasurable
    filter_upwards [hmem] with z hz
    rw [Real.norm_of_nonneg (le_max_right M 0)]
    exact (hM _ ⟨z,hz,rfl⟩).trans (le_max_left _ _)
  have hmean : (∫ x, G x ∂σ) ≤ J := by
    have hfub := integral_integral_swap (f := fun x z => Real.log ‖z-x‖) hmixed
    have hEq : (∫ x, G x ∂σ) = ∫ z, U z ∂μ := by
      unfold G U
      simp_rw [exteriorGreenCoordinate_eq_radial_potential F hF]
      simpa only [norm_sub_rev] using hfub
    rw [hEq]
    exact integral_mono_ae hUμ hdμ (.of_forall (fun x => (hσ x).2.2.1))
  apply FactorInequality_of_linear_families K hK hc C0
  intro n a
  let P : ℂ[X] := ∏ i : Fin n, (X-C (a i))
  let M := continuumPolynomialNorm K P
  have hM : 0 < M := exterior_linear_product_norm_pos F hF n a
  have hGpoly : ∀ᵐ z ∂σ, (∑ i : Fin n, Real.log ‖z-a i‖) ≤ Real.log M + (n:ℝ)*G z := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin n => (hσ (a i)).1)] with z hz
    have heval : ‖P.eval z‖ = ∏ i : Fin n, ‖z-a i‖ := by
      simp [P, eval_prod, eval_sub, norm_prod]
    have hpos : 0 < ‖P.eval z‖ := by
      rw [heval]
      exact Finset.prod_pos (fun i _ => norm_pos_iff.mpr (sub_ne_zero.mpr (hz i)))
    rw [← Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz i))), ← heval]
    by_cases hzE : z ∈ F '' exteriorDisk
    · obtain ⟨w,hw,rfl⟩ := hzE
      have hmem : F w ∈ F '' exteriorDisk := ⟨w,hw,rfl⟩
      have hB := exterior_linear_product_bernsteinWalsh F hF hc n a w hw
      have hl := Real.log_le_log hpos hB
      change Real.log ‖P.eval (F w)‖ ≤ Real.log (M * ‖w‖^n) at hl
      rw [Real.log_mul hM.ne' (pow_ne_zero _ (norm_ne_zero_iff.mpr (exterior_ne_zero hw))),
        Real.log_pow] at hl
      simp only [G, exteriorGreenCoordinate, if_pos hmem, exteriorInverse,
        hF.2.1.leftInvOn_invFunOn hw]
      exact hl
    · obtain ⟨y,hy,hmax⟩ := continuumPolynomialNorm_attained K hK hc P
      have hh : ‖P.eval z‖ ≤ M := by
        dsimp only [M]
        rw [continuumPolynomialNorm_eq_at_max K hK hc P hy hmax]
        exact hmax z hzE
      simpa only [G, exteriorGreenCoordinate, if_neg hzE, mul_zero, add_zero] using
        Real.log_le_log hpos hh
  have hiSum : Integrable (fun z => ∑ i : Fin n, Real.log ‖z-a i‖) σ :=
    integrable_finsetSum _ (fun i _ => (hσ (a i)).2.1)
  have hiG : Integrable (fun z => Real.log M + (n:ℝ)*G z) σ :=
    (integrable_const _).add (hGσ.const_mul _)
  have hI := integral_mono_ae hiSum hiG hGpoly
  rw [integral_finsetSum _ (fun i _ => (hσ (a i)).2.1),
    integral_add (integrable_const _) (hGσ.const_mul (n:ℝ)),
    integral_const, probReal_univ, one_smul, integral_const_mul] at hI
  change (∑ i : Fin n, U (a i)) ≤ Real.log M + (n:ℝ)*∫ x, G x ∂σ at hI
  have hfinal : (∑ i : Fin n, Real.log (d (a i))) ≤ Real.log M + (n:ℝ)*(J+ε) := by
    have hcomp := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
      (hσ (a i)).2.2.2)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hcomp
    have hh := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (α := ℝ) n)
    linarith
  change (∏ i : Fin n, d (a i)) ≤ C0^n * M
  apply (Real.log_le_log_iff (Finset.prod_pos (fun i _ => hd (a i)))
    (mul_pos (pow_pos (Real.exp_pos _) n) hM)).mp
  rw [Real.log_prod (fun i _ => (hd (a i)).ne'),
    Real.log_mul (pow_ne_zero _ (Real.exp_pos _).ne') hM.ne', Real.log_pow]
  simp only [C0, Real.log_exp]
  linarith

end SpringerLean
