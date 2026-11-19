import SpringerLean.Round1587EnergyTimeCoverage

namespace SpringerLean
set_option maxHeartbeats 1000000
noncomputable section

/-- A value and one-sided slope triple of the exact printed multiplier
at time t. Both adjacent slopes are permitted at a knot. -/
def EnergyMultiplierProfileAt
    (t : ℝ) (v : EnergyMultiplierValue) (cp fp sp : ℝ) : Prop :=
  v.t = t ∧
    ((∃ i : Fin 21, ∃ lam : ℝ,
        0 ≤ lam ∧ lam ≤ 1 ∧ v = energyMultiplierCellValue i lam ∧
        let j₀ : Fin 43 := ⟨2*i.val, by omega⟩
        let r₀ := energyMultiplierEndpointRaw j₀
        cp = r₀.cp ∧ fp = r₀.fp ∧ sp = r₀.sp) ∨
     (v = energyMultiplierTailValue t ∧
       let r := energyMultiplierEndpointRaw 42
       cp = r.cp ∧ fp = r.fp ∧ sp = r.sp))

/-- The printed piecewise affine profile exists at every nonnegative
time; at knots the existence theorem chooses either valid side. -/
theorem energyMultiplier_profile_exists (t : ℝ) (ht : 0 ≤ t) :
    ∃ v : EnergyMultiplierValue, ∃ cp fp sp : ℝ,
      EnergyMultiplierProfileAt t v cp fp sp := by
  rcases energyMultiplier_time_covered t ht with hcell | htail
  · obtain ⟨i, ht₀, ht₁⟩ := hcell
    obtain ⟨lam, hlam₀, hlam₁, htime⟩ :=
      energyMultiplier_cell_time_surjective i t ht₀ ht₁
    let r₀ := energyMultiplierEndpointRaw (⟨2*i.val, by omega⟩ : Fin 43)
    refine ⟨energyMultiplierCellValue i lam, r₀.cp, r₀.fp, r₀.sp, ?_⟩
    refine ⟨htime, Or.inl ?_⟩
    exact ⟨i, lam, hlam₀, hlam₁, rfl, rfl, rfl, rfl⟩
  · let r := energyMultiplierEndpointRaw 42
    refine ⟨energyMultiplierTailValue t, r.cp, r.fp, r.sp, ?_⟩
    refine ⟨rfl, Or.inr ?_⟩
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The 43 rational endpoint certificates now bound the original
multiplier quadratic at every real t ≥ 0, for every valid one-sided
choice of slope and every k ≥ 751. -/
theorem energyMultiplier_allK_allTime_quadratic
    {k : ℕ} (hk : 751 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    {v : EnergyMultiplierValue} {cp fp sp s : ℝ}
    (hprofile : EnergyMultiplierProfileAt t v cp fp sp)
    (hs : 0 ≤ s) :
    signedEnergyQuadratic
      (energyMultiplierA (1/(k:ℝ)) fp sp v)
      (energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) cp fp sp v)
      (energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) cp v) s ≤ 25/16 := by
  obtain ⟨-, hbranch⟩ := hprofile
  rcases hbranch with hcell | htail
  · obtain ⟨i, lam, hlam₀, hlam₁, hv, hcp, hfp, hsp⟩ := hcell
    subst v
    rw [hcp, hfp, hsp]
    exact energyMultiplier_allK_finiteCell_quadratic hk i hlam₀ hlam₁ hs
  · obtain ⟨hv, hcp, hfp, hsp⟩ := htail
    subst v
    rw [hcp, hfp, hsp]
    exact energyMultiplier_allK_tail_quadratic hk hs

end
end SpringerLean

#print axioms SpringerLean.energyMultiplier_profile_exists
#print axioms SpringerLean.energyMultiplier_allK_allTime_quadratic
