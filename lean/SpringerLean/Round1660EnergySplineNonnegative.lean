import SpringerLean.Round1632ExplicitEnergyProfile

namespace SpringerLean

/-- The finite multiplier table is nonnegative after interpolation;
slopes may have either sign, so the endpoint values are used. -/
theorem energyMultiplierCellValue_nonneg
    (i : Fin 21) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    0 ≤ (energyMultiplierCellValue i lam).chi ∧
    0 ≤ (energyMultiplierCellValue i lam).f ∧
    0 ≤ (energyMultiplierCellValue i lam).sigma := by
  let j0 : Fin 43 := ⟨2*i.val, by omega⟩
  let j1 : Fin 43 := ⟨2*i.val+1, by omega⟩
  have hleft := energyMultiplierEndpointRaw_nonneg_all43 j0
  have hright := energyMultiplierEndpointRaw_nonneg_all43 j1
  have hc0 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j0).chi := by
    exact_mod_cast hleft.2.1
  have hf0 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j0).f := by
    exact_mod_cast hleft.2.2.1
  have hs0 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j0).sigma := by
    exact_mod_cast hleft.2.2.2
  have hc1 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j1).chi := by
    exact_mod_cast hright.2.1
  have hf1 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j1).f := by
    exact_mod_cast hright.2.2.1
  have hs1 : (0:ℝ) ≤ (energyMultiplierEndpointRaw j1).sigma := by
    exact_mod_cast hright.2.2.2
  have ha : 0 ≤ 1-lam := by linarith
  refine ⟨?_, ?_, ?_⟩
  · change 0 ≤ (1-lam)*(energyMultiplierEndpointRaw j0).chi+
      lam*(energyMultiplierEndpointRaw j1).chi
    exact add_nonneg (mul_nonneg ha hc0) (mul_nonneg h0 hc1)
  · change 0 ≤ (1-lam)*(energyMultiplierEndpointRaw j0).f+
      lam*(energyMultiplierEndpointRaw j1).f
    exact add_nonneg (mul_nonneg ha hf0) (mul_nonneg h0 hf1)
  · change 0 ≤ (1-lam)*(energyMultiplierEndpointRaw j0).sigma+
      lam*(energyMultiplierEndpointRaw j1).sigma
    exact add_nonneg (mul_nonneg ha hs0) (mul_nonneg h0 hs1)

/-- All three explicit global multiplier values stay nonnegative at
every physical time t>=0. -/
theorem energyMultiplierSpline_nonneg
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ energyMultiplierChi t ∧
    0 ≤ energyMultiplierF t ∧
    0 ≤ energyMultiplierSigma t := by
  obtain ⟨cp, fp, sp, hp⟩ := energyMultiplierSpline_profile_exists t ht
  obtain ⟨-, hbranch⟩ := hp
  rcases hbranch with hcell | htail
  · obtain ⟨i, lam, hl0, hl1, hv, -, -, -⟩ := hcell
    have h := energyMultiplierCellValue_nonneg i hl0 hl1
    rw [← hv] at h
    exact h
  · obtain ⟨hv, -, -, -⟩ := htail
    change 0 ≤ (energyMultiplierSplineValue t).chi ∧
      0 ≤ (energyMultiplierSplineValue t).f ∧
      0 ≤ (energyMultiplierSplineValue t).sigma
    rw [hv]
    have h := energyMultiplierEndpointRaw_nonneg_all43 (42 : Fin 43)
    refine ⟨?_, ?_, ?_⟩
    · change (0:ℝ) ≤ ((energyMultiplierEndpointRaw 42).chi:ℝ)
      exact_mod_cast h.2.1
    · change (0:ℝ) ≤ ((energyMultiplierEndpointRaw 42).f:ℝ)
      exact_mod_cast h.2.2.1
    · change (0:ℝ) ≤ ((energyMultiplierEndpointRaw 42).sigma:ℝ)
      exact_mod_cast h.2.2.2

end SpringerLean

#print axioms SpringerLean.energyMultiplierCellValue_nonneg
#print axioms SpringerLean.energyMultiplierSpline_nonneg
