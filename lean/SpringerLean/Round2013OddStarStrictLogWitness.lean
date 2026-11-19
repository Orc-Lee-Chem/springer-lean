import SpringerLean.Round2012OddStarOppositeTipMembership

namespace SpringerLean
open scoped Topology

theorem exists_positive_increase_in_nhds
    (f : ℝ → ℝ) (d : ℝ)
    (hd : 0 < d) (hderiv : HasDerivAt f d 0)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧ f 0 < f t := by
  have hlim := hderiv.tendsto_slope_zero_right
  have hslope : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      0 < t⁻¹ * (f (0 + t) - f 0) := by
    exact hlim.eventually (Ioi_mem_nhds hd)
  have hU' : U ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)) hU
  obtain ⟨t, ⟨hsl, htpos⟩, htU⟩ :=
    ((hslope.and (self_mem_nhdsWithin : Set.Ioi 0 ∈ 𝓝[>] (0 : ℝ))).and
      hU').exists
  have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
  have hdiff : 0 < f t - f 0 := by
    have hsl' : 0 < t⁻¹ * (f t - f 0) := by simpa using hsl
    exact (mul_pos_iff_of_pos_left hinvpos).mp hsl'
  exact ⟨t, htU, htpos, sub_pos.mp hdiff⟩

theorem oddStarOppositeTipLogDistance_integral_strict_increase_near_zero
    (m : ℕ) (hm : 3 ≤ m)
    (U : Set ℝ) (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ t ∈ U, 0 < t ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogDistance m θ 0) <
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogDistance m θ t) := by
  let A : ℝ → ℝ := fun t =>
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarOppositeTipLogDistance m θ t
  let d : ℝ := ∫ θ in (0 : ℝ)..2 * Real.pi,
    oddStarOppositeTipLogSlope m θ 0
  have hderiv : HasDerivAt A d 0 :=
    oddStarOppositeTipLogDistance_integral_hasDerivAt_zero m hm
  have hd : 0 < d := by
    have h := oddStarOppositeTipLogDistance_integral_deriv_strict_pos m hm
    change 0 < deriv A 0 at h
    rw [hderiv.deriv] at h
    exact h
  exact exists_positive_increase_in_nhds A d hd hderiv U hU

theorem oddStarActualContinuum_exists_strict_log_variation
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ t : ℝ, 0 < t ∧ |t| < 1 ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t ∈
          oddStarPerturbationOmitted m t) ∧
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ∈
          oddStarPerturbationOmitted m t ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogDistance m θ 0) <
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogDistance m θ t) := by
  obtain ⟨U, hU, hZ⟩ :=
    oddStarMovingBoundaryPoint_uniform_mem_omitted m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  obtain ⟨t, ht, htpos, hinc⟩ :=
    oddStarOppositeTipLogDistance_integral_strict_increase_near_zero
      m hm (U ∩ V) (Filter.inter_mem hU hV)
  have ht1 : |t| < 1 := by
    simpa [V, abs_lt] using ht.2
  exact ⟨t, htpos, ht1, hZ t ht.1,
    oddStarOppositeTip_mem_omitted m hm hodd t ht1, hinc⟩

end SpringerLean
