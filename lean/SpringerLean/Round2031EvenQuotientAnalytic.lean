import SpringerLean.Round2030EvenActualQuotientGeometry

open scoped Topology

namespace SpringerLean

theorem evenExteriorPowerQuotient_analyticAt
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hcov : EvenExteriorCovariant F k)
    (v : ℂ) (hv : v ∈ exteriorDisk) :
    AnalyticAt ℂ (evenExteriorPowerQuotient F k) v := by
  let z : ℂ := v ^ ((k:ℂ)⁻¹)
  have hzpow : z ^ k = v := by
    simpa only [z] using Complex.cpow_nat_inv_pow v (by omega : k ≠ 0)
  have hz : z ∈ exteriorDisk := by
    have hnormpow : ‖z‖ ^ k = ‖v‖ := by rw [← norm_pow, hzpow]
    have hpowgt : 1 < ‖z‖ ^ k := by rw [hnormpow]; exact hv
    exact (one_lt_pow_iff_of_nonneg (norm_nonneg z)
      (by omega : k ≠ 0)).mp hpowgt
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq, exteriorDisk] at hz
    norm_num at hz
  let P : ℂ → ℂ := fun w => w ^ k
  have hPa : AnalyticAt ℂ P z := by fun_prop
  have hPd : HasStrictDerivAt P ((k:ℂ) * z ^ (k-1)) z := by
    simpa [P] using hasStrictDerivAt_pow k z
  have hPder : deriv P z ≠ 0 := by
    rw [hPd.hasDerivAt.deriv]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hk))
      (pow_ne_zero _ hz0)
  let R : ℂ → ℂ := hPa.hasStrictDerivAt.localInverse P (deriv P z) z hPder
  have hR0 : R v = z := by
    rw [← hzpow]
    exact HasStrictFDerivAt.localInverse_apply_image
      (hPa.hasStrictDerivAt.hasStrictFDerivAt_equiv hPder)
  have hRa : AnalyticAt ℂ R v := by
    rw [← hzpow]
    exact hPa.analyticAt_localInverse hPder
  have hRext : ∀ᶠ u in 𝓝 v, R u ∈ exteriorDisk := by
    apply hRa.continuousAt.eventually
    rw [hR0]
    exact exteriorDisk_isOpen.mem_nhds hz
  have hright : ∀ᶠ u in 𝓝 v, (R u)^k = u := by
    rw [← hzpow]
    exact hPa.hasStrictDerivAt.eventually_right_inverse hPder
  have hFa : AnalyticAt ℂ F (R v) := by
    rw [hR0]
    exact hF.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hComp : AnalyticAt ℂ (fun u : ℂ => (F (R u))^k) v := by
    have hh : AnalyticAt ℂ (fun u : ℂ => F (R u)) v :=
      AnalyticAt.comp (f := R) hFa hRa
    exact hh.pow k
  have hEq : (fun u : ℂ => (F (R u))^k) =ᶠ[𝓝 v]
      evenExteriorPowerQuotient F k := by
    filter_upwards [hRext, hright] with u hu hPu
    have hPrincipal : (u ^ ((k:ℂ)⁻¹))^k = u :=
      Complex.cpow_nat_inv_pow u (by omega : k ≠ 0)
    have hFiber := evenExterior_power_fiber_eq F k hcov
      (u ^ ((k:ℂ)⁻¹)) (R u) hu (hPrincipal.trans hPu.symm)
    exact hFiber.symm
  exact hComp.congr hEq

/-- For a symmetric actual omitted continuum, the power quotient is
holomorphic throughout the open exterior disk. The centered germ at
infinity is a separate obligation. -/
theorem evenExteriorPowerQuotient_actual_differentiableOn
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    DifferentiableOn ℂ (evenExteriorPowerQuotient F k) exteriorDisk := by
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  intro v hv
  exact (evenExteriorPowerQuotient_analyticAt F k hk hF hcov v hv).differentiableAt.differentiableWithinAt

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_actual_differentiableOn
