import SpringerLean.Round2031EvenQuotientAnalytic

open Filter
open scoped Topology

namespace SpringerLean

noncomputable def evenQuotientReciprocalRoot (k : ℕ) (t : ℂ) : ℂ :=
  ((t⁻¹) ^ ((k:ℂ)⁻¹))⁻¹

theorem evenQuotientReciprocalRoot_pow
    (k : ℕ) (hk : 0 < k) (t : ℂ) :
    (evenQuotientReciprocalRoot k t)^k = t := by
  unfold evenQuotientReciprocalRoot
  rw [inv_pow, Complex.cpow_nat_inv_pow _ (by omega : k ≠ 0), inv_inv]

theorem evenQuotientReciprocalRoot_tendsto_zero
    (k : ℕ) (hk : 0 < k) :
    Tendsto (evenQuotientReciprocalRoot k) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε^k := pow_pos hε _
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Metric.ball_mem_nhds (0:ℂ) hδ)] with t ht
  have htnorm : ‖t‖ < ε^k := by simpa using ht
  have hnormpow : ‖evenQuotientReciprocalRoot k t‖^k = ‖t‖ := by
    rw [← norm_pow, evenQuotientReciprocalRoot_pow k hk]
  have hnorm : ‖evenQuotientReciprocalRoot k t‖ < ε :=
    lt_of_pow_lt_pow_left₀ k hε.le (by rwa [hnormpow])
  simpa using hnorm

theorem evenQuotient_exteriorPhi_punctured
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (t : ℂ) (ht0 : t ≠ 0) :
    exteriorPhi (evenExteriorPowerQuotient F k) t =
      (exteriorPhi F (evenQuotientReciprocalRoot k t))^k := by
  let z : ℂ := (t⁻¹) ^ ((k:ℂ)⁻¹)
  let u : ℂ := evenQuotientReciprocalRoot k t
  have hzpow : z^k = t⁻¹ := by
    simpa only [z] using Complex.cpow_nat_inv_pow t⁻¹ (by omega : k ≠ 0)
  have hz0 : z ≠ 0 := by
    intro heq
    rw [heq, zero_pow (by omega : k ≠ 0)] at hzpow
    exact (inv_ne_zero ht0) hzpow.symm
  have hu0 : u ≠ 0 := inv_ne_zero hz0
  have huinv : u⁻¹ = z := by simp [u, z, evenQuotientReciprocalRoot]
  have hFz : F z = z * exteriorPhi F u := by
    have h := exteriorF_reciprocal_phi F hu0
    simpa only [huinv] using h
  have hGphi : exteriorPhi (evenExteriorPowerQuotient F k) t =
      t * evenExteriorPowerQuotient F k t⁻¹ := by
    rw [exteriorPhi, exteriorForwardGerm_punctured _ ht0]
    field_simp [ht0]
    ring
  have hGval : evenExteriorPowerQuotient F k t⁻¹ = (F z)^k := by
    rfl
  calc
    exteriorPhi (evenExteriorPowerQuotient F k) t =
        t * evenExteriorPowerQuotient F k t⁻¹ := hGphi
    _ = t * (F z)^k := by rw [hGval]
    _ = t * (z * exteriorPhi F u)^k := by rw [hFz]
    _ = (t * z^k) * (exteriorPhi F u)^k := by rw [mul_pow]; ring
    _ = (exteriorPhi F u)^k := by rw [hzpow, mul_inv_cancel₀ ht0, one_mul]

theorem evenQuotient_exteriorPhi_tendsto_one
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 0 < k) :
    Tendsto (exteriorPhi (evenExteriorPowerQuotient F k))
      (𝓝[≠] (0:ℂ)) (𝓝 1) := by
  have hroot := evenQuotientReciprocalRoot_tendsto_zero k hk
  have hphi := (exteriorPhi_analyticAt F hF.2.2).continuousAt.tendsto.comp hroot
  have hpow := hphi.pow k
  have hEq : exteriorPhi (evenExteriorPowerQuotient F k) =ᶠ[𝓝[≠] (0:ℂ)]
      (fun t => (exteriorPhi F (evenQuotientReciprocalRoot k t))^k) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact evenQuotient_exteriorPhi_punctured F k hk t ht
  have hlimit : (exteriorPhi F 0)^k = (1:ℂ) := by
    simp [exteriorPhi_zero]
  rw [hlimit] at hpow
  exact hpow.congr' hEq.symm

theorem exteriorPhi_analyticAt_zero_of_exterior_holomorphic
    (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G exteriorDisk)
    (hLimit : Tendsto (exteriorPhi G) (𝓝[≠] (0:ℂ)) (𝓝 1)) :
    AnalyticAt ℂ (exteriorPhi G) 0 := by
  have hCont : ContinuousAt (exteriorPhi G) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    simpa only [exteriorPhi_zero] using hLimit
  have hDiff : ∀ᶠ t in 𝓝[≠] (0:ℂ),
      DifferentiableAt ℂ (exteriorPhi G) t := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1)),
      self_mem_nhdsWithin] with t ht ht0
    have htNorm : ‖t‖ < 1 := by simpa using ht
    have htPos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have htInv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      have h := one_div_lt_one_div_of_lt htPos htNorm
      simpa [one_div] using h
    have hTa : AnalyticAt ℂ (fun s : ℂ => s⁻¹) t := analyticAt_inv ht0
    have hGa : AnalyticAt ℂ G t⁻¹ :=
      hG.analyticAt (exteriorDisk_isOpen.mem_nhds htInv)
    have hComp : AnalyticAt ℂ (fun s : ℂ => G s⁻¹) t :=
      AnalyticAt.comp (f := fun s : ℂ => s⁻¹) hGa hTa
    have hProd : AnalyticAt ℂ (fun s : ℂ => s * G s⁻¹) t :=
      analyticAt_id.mul hComp
    have hEq : (fun s : ℂ => s * G s⁻¹) =ᶠ[𝓝 t] exteriorPhi G := by
      filter_upwards [continuousAt_id.eventually_ne ht0] with s hs
      have hs0 : s ≠ 0 := by simpa only [id_eq] using hs
      rw [exteriorPhi, exteriorForwardGerm_punctured G hs0]
      field_simp [hs0]
      ring
    exact (hProd.congr hEq).differentiableAt
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hDiff hCont

theorem evenQuotient_exteriorPhi_analyticAt_zero
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    AnalyticAt ℂ (exteriorPhi (evenExteriorPowerQuotient F k)) 0 := by
  exact exteriorPhi_analyticAt_zero_of_exterior_holomorphic _
    (evenExteriorPowerQuotient_actual_differentiableOn
      F K k hk hF hK hImage)
    (evenQuotient_exteriorPhi_tendsto_one F hF k hk)

theorem exteriorPhi_even_near_zero_of_odd
    (G : ℂ → ℂ)
    (hOdd : ∀ v ∈ exteriorDisk, G (-v) = -G v)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) :
    exteriorPhi G (-t) = exteriorPhi G t := by
  by_cases ht0 : t = 0
  · simp [ht0]
  · have htNorm : ‖t‖ < 1 := by simpa using ht
    have htPos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have htInv : t⁻¹ ∈ exteriorDisk := by
      change 1 < ‖t⁻¹‖
      rw [norm_inv]
      have hh := one_div_lt_one_div_of_lt htPos htNorm
      simpa [one_div] using hh
    have hneg : -t ≠ 0 := neg_ne_zero.mpr ht0
    have hphi (u : ℂ) (hu : u ≠ 0) :
        exteriorPhi G u = u * G u⁻¹ := by
      rw [exteriorPhi, exteriorForwardGerm_punctured G hu]
      field_simp [hu]
      ring
    rw [hphi (-t) hneg, hphi t ht0, inv_neg, hOdd t⁻¹ htInv]
    ring

theorem exteriorPhi_deriv_zero_of_odd
    (G : ℂ → ℂ)
    (hOdd : ∀ v ∈ exteriorDisk, G (-v) = -G v) :
    deriv (exteriorPhi G) 0 = 0 := by
  have hEven : (fun t : ℂ => exteriorPhi G (-t)) =ᶠ[𝓝 (0:ℂ)]
      exteriorPhi G := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ)
      (by norm_num : (0:ℝ)<1)] with t ht
    exact exteriorPhi_even_near_zero_of_odd G hOdd t ht
  have hd := hEven.deriv_eq
  rw [deriv_comp_neg] at hd
  simpa only [neg_zero, CharZero.neg_eq_self_iff] using hd

theorem exteriorForwardGerm_eq_dslope_of_phi_deriv_zero
    (G : ℂ → ℂ) (hDeriv : deriv (exteriorPhi G) 0 = 0) :
    exteriorForwardGerm G = dslope (exteriorPhi G) 0 := by
  funext t
  by_cases ht : t = 0
  · subst t
    simp [exteriorForwardGerm, dslope_same, hDeriv]
  · rw [dslope_of_ne _ ht, slope_def_module]
    rw [exteriorForwardGerm_punctured G ht]
    simp [exteriorPhi,
      exteriorForwardGerm_punctured G ht]
    field_simp [ht]

theorem exteriorForwardGerm_analyticAt_of_phi_analytic_and_odd
    (G : ℂ → ℂ)
    (hPhi : AnalyticAt ℂ (exteriorPhi G) 0)
    (hOdd : ∀ v ∈ exteriorDisk, G (-v) = -G v) :
    AnalyticAt ℂ (exteriorForwardGerm G) 0 := by
  obtain ⟨r, hr, hOn⟩ := hPhi.exists_ball_analyticOnNhd
  have hDiff : DifferentiableOn ℂ (exteriorPhi G)
      (Metric.ball (0:ℂ) r) := by
    intro t ht
    exact (hOn t ht).differentiableAt.differentiableWithinAt
  have hDslope : DifferentiableOn ℂ (dslope (exteriorPhi G) 0)
      (Metric.ball (0:ℂ) r) :=
    (Complex.differentiableOn_dslope
      (Metric.ball_mem_nhds (0:ℂ) hr)).mpr hDiff
  have hDa : AnalyticAt ℂ (dslope (exteriorPhi G) 0) 0 :=
    hDslope.analyticAt (Metric.ball_mem_nhds (0:ℂ) hr)
  rw [exteriorForwardGerm_eq_dslope_of_phi_deriv_zero G
    (exteriorPhi_deriv_zero_of_odd G hOdd)]
  exact hDa

theorem evenExteriorPowerQuotient_actual_centered
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    CenteredExteriorUnivalent (evenExteriorPowerQuotient F k) := by
  have hGeom := evenExteriorPowerQuotient_actual_geometry
    F K k hk hF hK hImage
  exact ⟨evenExteriorPowerQuotient_actual_differentiableOn
      F K k hk hF hK hImage,
    hGeom.1,
    exteriorForwardGerm_analyticAt_of_phi_analytic_and_odd _
      (evenQuotient_exteriorPhi_analyticAt_zero
        F K k hk hF hK hImage) hGeom.2.2⟩

/-- The actual symmetric quotient now satisfies the odd-map second
moment margin with no separate quotient-class premise. -/
theorem evenExteriorPowerQuotient_actual_secondMoment
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    actualBoundaryRadialMoment (evenExteriorPowerQuotient F k) 2 ≤
      2 - (2/3:ℝ) *
        (1 - ‖exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1‖^2) :=
  evenExteriorPowerQuotient_actual_secondMoment_of_centered
    F K k hk hF hK hImage
    (evenExteriorPowerQuotient_actual_centered F K k hk hF hK hImage)

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_actual_centered
#print axioms SpringerLean.evenExteriorPowerQuotient_actual_secondMoment
