import SpringerLean.ExteriorClass

open scoped Topology

namespace SpringerLean

/-- The normalized forward factor at infinity. -/
noncomputable def exteriorPhi (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  1 + u * exteriorForwardGerm F u

/-- Reciprocal coordinate of the actual forward exterior map. -/
noncomputable def exteriorH (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  u / exteriorPhi F u

theorem exteriorPhi_zero (F : ℂ → ℂ) : exteriorPhi F 0 = 1 := by
  simp [exteriorPhi]

theorem exteriorH_zero (F : ℂ → ℂ) : exteriorH F 0 = 0 := by
  simp [exteriorH]

theorem exteriorPhi_analyticAt (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    AnalyticAt ℂ (exteriorPhi F) 0 := by
  unfold exteriorPhi
  fun_prop

theorem exteriorPhi_eventually_ne_zero (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    ∀ᶠ u in 𝓝 (0 : ℂ), exteriorPhi F u ≠ 0 :=
  (exteriorPhi_analyticAt F hf).continuousAt.eventually_ne (by simp [exteriorPhi])

theorem exteriorH_analyticAt (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    AnalyticAt ℂ (exteriorH F) 0 := by
  have h := (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) 0).div
    (exteriorPhi_analyticAt F hf) (by simp [exteriorPhi])
  convert h using 1
  funext u
  rfl

theorem exteriorH_hasDerivAt (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    HasDerivAt (exteriorH F) 1 0 := by
  have hg : DifferentiableAt ℂ (exteriorForwardGerm F) 0 := hf.differentiableAt
  have hmul : HasDerivAt
      (fun u : ℂ => u * exteriorForwardGerm F u) 0 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt using 1
    · funext u; rfl
    · simp [exteriorForwardGerm]
  have hphi : HasDerivAt (exteriorPhi F) 0 0 := by
    convert (hasDerivAt_const (0 : ℂ) (1 : ℂ)).add hmul using 1
    · funext u; rfl
    · simp
  convert (hasDerivAt_id (0 : ℂ)).div hphi (by simp [exteriorPhi]) using 1
  · funext u; rfl
  · simp [exteriorPhi]

theorem exteriorH_deriv (F : ℂ → ℂ)
    (hf : AnalyticAt ℂ (exteriorForwardGerm F) 0) :
    deriv (exteriorH F) 0 = 1 :=
  (exteriorH_hasDerivAt F hf).deriv

/-- The reciprocal coordinate agrees with the actual forward map near infinity. -/
theorem exteriorH_eq_inv_forward (F : ℂ → ℂ) {u : ℂ}
    (hu : u ≠ 0) (hphi : exteriorPhi F u ≠ 0) :
    exteriorH F u = (F u⁻¹)⁻¹ := by
  have hmul : u * F u⁻¹ = exteriorPhi F u := by
    rw [exteriorPhi, exteriorForwardGerm_punctured F hu]
    field_simp [hu]
    ring
  have hF0 : F u⁻¹ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact hphi hmul.symm
  rw [exteriorH, ← hmul]
  field_simp [hu, hF0]

/-- The analytic local inverse of H at zero, with the neighborhood facts
needed to identify it with the actual exterior inverse. -/
theorem exteriorH_localInverse (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    ∃ V : ℂ → ℂ,
      V 0 = 0 ∧
      AnalyticAt ℂ V 0 ∧
      deriv V 0 = 1 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), exteriorH F (V t) = t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), ‖V t‖ < 1) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), exteriorPhi F (V t) ≠ 0) := by
  let hh := exteriorH_analyticAt F hc.2.2
  have hd : deriv (exteriorH F) 0 ≠ 0 := by
    rw [exteriorH_deriv F hc.2.2]
    exact one_ne_zero
  let V := hh.hasStrictDerivAt.localInverse _ _ _ hd
  have hVimage : V (exteriorH F 0) = 0 :=
    HasStrictFDerivAt.localInverse_apply_image ..
  have hV0 : V 0 = 0 := by simpa only [exteriorH_zero] using hVimage
  have hVa : AnalyticAt ℂ V 0 := by
    simpa only [exteriorH_zero] using hh.analyticAt_localInverse hd
  have hVder : deriv V 0 = 1 := by
    have h : HasStrictDerivAt V (deriv (exteriorH F) 0)⁻¹ (exteriorH F 0) :=
      hh.hasStrictDerivAt.to_localInverse hd
    simpa [exteriorH_zero, exteriorH_deriv F hc.2.2] using h.hasDerivAt.deriv
  have hright : ∀ᶠ t in 𝓝 (0 : ℂ), exteriorH F (V t) = t := by
    simpa only [exteriorH_zero] using hh.hasStrictDerivAt.eventually_right_inverse hd
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℂ), ‖V t‖ < 1 := by
    have hopen : IsOpen {z : ℂ | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
    exact hVa.continuousAt.eventually (hopen.mem_nhds (by simp [hV0]))
  have hVtendsto : Filter.Tendsto V (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hV0] using hVa.continuousAt.tendsto
  have hphiV : ∀ᶠ t in 𝓝 (0 : ℂ), exteriorPhi F (V t) ≠ 0 :=
    hVtendsto.eventually (exteriorPhi_eventually_ne_zero F hc.2.2)
  exact ⟨V, hV0, hVa, hVder, hright, hsmall, hphiV⟩
/-- The local inverse of H is the actual exterior inverse branch.
The final equality is the reusable analytic-germ bridge. -/
theorem exterior_actualInverse_local_branch (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    ∃ V : ℂ → ℂ,
      V 0 = 0 ∧
      AnalyticAt ℂ V 0 ∧
      deriv V 0 = 1 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), exteriorH F (V t) = t) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
        V t ≠ 0 ∧
        (V t)⁻¹ ∈ exteriorDisk ∧
        F (V t)⁻¹ = t⁻¹ ∧
        exteriorInverse F t⁻¹ = (V t)⁻¹) ∧
      exteriorInverseGerm F =ᶠ[𝓝 (0 : ℂ)]
        (fun t => exteriorForwardGerm F (V t)) := by
  rcases exteriorH_localInverse F hc with
    ⟨V, hV0, hVa, hVder, hright, hsmall, hphiV⟩
  have hbranch : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
      V t ≠ 0 ∧
      (V t)⁻¹ ∈ exteriorDisk ∧
      F (V t)⁻¹ = t⁻¹ ∧
      exteriorInverse F t⁻¹ = (V t)⁻¹ := by
    filter_upwards [hright, hsmall, hphiV] with t hrt hsm hph ht
    have hvne : V t ≠ 0 := by
      intro hv
      rw [hv, exteriorH_zero] at hrt
      exact ht hrt.symm
    have hvext : (V t)⁻¹ ∈ exteriorDisk := by
      change 1 < ‖(V t)⁻¹‖
      rw [norm_inv]
      have hvpos : (0 : ℝ) < ‖V t‖ := norm_pos_iff.mpr hvne
      have h := one_div_lt_one_div_of_lt hvpos hsm
      simpa only [one_div, inv_one] using h
    have hF : F (V t)⁻¹ = t⁻¹ := by
      have heq : (F (V t)⁻¹)⁻¹ = t :=
        (exteriorH_eq_inv_forward F hvne hph).symm.trans hrt
      have heq' := congrArg Inv.inv heq
      simpa only [inv_inv] using heq'
    have hInv : exteriorInverse F t⁻¹ = (V t)⁻¹ := by
      have h := hc.2.1.leftInvOn_invFunOn hvext
      simpa only [exteriorInverse, hF] using h
    exact ⟨hvne, hvext, hF, hInv⟩
  have hcomp : exteriorInverseGerm F =ᶠ[𝓝 (0 : ℂ)]
      (fun t => exteriorForwardGerm F (V t)) := by
    filter_upwards [hbranch] with t hbt
    by_cases ht : t = 0
    · subst t
      simp [exteriorInverseGerm, exteriorForwardGerm, hV0]
    · obtain ⟨hvne, hvext, hF, hInv⟩ := hbt ht
      rw [exteriorForwardGerm_punctured F hvne]
      simp [exteriorInverseGerm, ht, hInv, hF]
  exact ⟨V, hV0, hVa, hVder, hright, hbranch, hcomp⟩

/-- Every sufficiently large reciprocal target lies in the actual image. -/
theorem exterior_inverse_covers_near_infinity (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → t⁻¹ ∈ F '' exteriorDisk := by
  rcases exterior_actualInverse_local_branch F hc with
    ⟨V, hV0, hVa, hVder, hright, hbranch, hcomp⟩
  filter_upwards [hbranch] with t hbt ht
  obtain ⟨hvne, hvext, hF, hInv⟩ := hbt ht
  exact ⟨(V t)⁻¹, hvext, hF⟩

/-- The inverse correction of each paper-class map is an actual analytic germ. -/
theorem exteriorInverseGerm_analyticAt (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    AnalyticAt ℂ (exteriorInverseGerm F) 0 := by
  rcases exterior_actualInverse_local_branch F hc with
    ⟨V, hV0, hVa, hVder, hright, hbranch, hcomp⟩
  have hf := hc.2.2
  have hfa : AnalyticAt ℂ (fun t => exteriorForwardGerm F (V t)) 0 := by
    have hf' : AnalyticAt ℂ (exteriorForwardGerm F) (V 0) := by
      simpa only [hV0] using hf
    simpa only [Function.comp_def] using hf'.comp hVa
  exact hfa.congr hcomp.symm

/-- Unconditional B₁=b₁ for every actual centered exterior univalent map. -/
theorem exteriorInverseCoeff_one_eq_forwardCoeff_one (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 1 = exteriorForwardCoeff F 1 :=
  exteriorInverseCoeff_one_eq_forwardCoeff_one_of_local F
    hc.2.2.differentiableAt
    (exteriorInverseGerm_analyticAt F hc).differentiableAt
    (exterior_inverse_covers_near_infinity F hc)
/-- Functional equations for the same local inverse and actual inverse correction.
These are the starting point for all-order coefficient reversion. -/
theorem exterior_inverse_functional_germs (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    ∃ V : ℂ → ℂ,
      V 0 = 0 ∧ AnalyticAt ℂ V 0 ∧ deriv V 0 = 1 ∧
      (∀ᶠ t in 𝓝 (0 : ℂ),
        V t = t * exteriorPhi F (V t) ∧
        exteriorInverseGerm F t = exteriorForwardGerm F (V t)) := by
  rcases exterior_actualInverse_local_branch F hc with
    ⟨V, hV0, hVa, hVder, hright, hbranch, hcomp⟩
  have hVtendsto : Filter.Tendsto V (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hV0] using hVa.continuousAt.tendsto
  have hphiV : ∀ᶠ t in 𝓝 (0 : ℂ), exteriorPhi F (V t) ≠ 0 :=
    hVtendsto.eventually (exteriorPhi_eventually_ne_zero F hc.2.2)
  refine ⟨V, hV0, hVa, hVder, ?_⟩
  filter_upwards [hright, hphiV, hcomp] with t hrt hph hcp
  constructor
  · exact (div_eq_iff hph).mp (show V t / exteriorPhi F (V t) = t by
      simpa only [exteriorH] using hrt)
  · exact hcp

theorem exteriorInverseCoeff_zero (F : ℂ → ℂ) :
    exteriorInverseCoeff F 0 = 0 := by
  simp [exteriorInverseCoeff, exteriorInverseGerm]

/-- All actual inverse Laurent coefficients are read by a convergent Taylor
series, independently of any proposed coefficient formula. -/
theorem exteriorInverseGerm_hasSum_coeff (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => exteriorInverseCoeff F n * t ^ n)
        (exteriorInverseGerm F t) := by
  have hp := (exteriorInverseGerm_analyticAt F hc).hasFPowerSeriesAt
  have hs := hasFPowerSeriesAt_iff.mp hp
  filter_upwards [hs] with t ht
  simpa [FormalMultilinearSeries.coeff_ofScalars, exteriorInverseCoeff,
    smul_eq_mul, mul_comm] using ht
/-- Exact algebraic relation between the actual F and its normalized factor. -/
theorem exteriorF_reciprocal_phi (F : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    F u⁻¹ = u⁻¹ * exteriorPhi F u := by
  rw [exteriorPhi, exteriorForwardGerm_punctured F hu]
  field_simp [hu]
  ring

theorem exteriorF_pow_reciprocal_phi (F : ℂ → ℂ) {u : ℂ}
    (hu : u ≠ 0) (n : ℕ) :
    (F u⁻¹) ^ n = (u⁻¹) ^ n * (exteriorPhi F u) ^ n := by
  rw [exteriorF_reciprocal_phi F hu, mul_pow]
end SpringerLean