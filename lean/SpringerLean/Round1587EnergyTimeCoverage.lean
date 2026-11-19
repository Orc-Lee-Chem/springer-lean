import SpringerLean.Round1586EnergyCellEndpointBridge

namespace SpringerLean
set_option maxHeartbeats 1000000
noncomputable section

/-- Every nonnegative time lies in a printed finite cell or in the constant tail. -/
theorem energyMultiplier_time_covered (t : ℝ) (ht : 0 ≤ t) :
    (∃ i : Fin 21,
      (energyMultiplierValueRaw (⟨2*i.val, by omega⟩ : Fin 43)).t ≤ t ∧
      t ≤ (energyMultiplierValueRaw (⟨2*i.val+1, by omega⟩ : Fin 43)).t) ∨
    (energyMultiplierEndpointRaw 42).t ≤ t := by
  by_cases h0 : t ≤ (1:ℝ)/60
  · left
    refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h1 : t ≤ (2:ℝ)/60
  · left
    refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h2 : t ≤ (3:ℝ)/60
  · left
    refine ⟨⟨2, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h3 : t ≤ (4:ℝ)/60
  · left
    refine ⟨⟨3, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h4 : t ≤ (5:ℝ)/60
  · left
    refine ⟨⟨4, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h5 : t ≤ (6:ℝ)/60
  · left
    refine ⟨⟨5, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h6 : t ≤ (7:ℝ)/60
  · left
    refine ⟨⟨6, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h7 : t ≤ (8:ℝ)/60
  · left
    refine ⟨⟨7, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h8 : t ≤ (9:ℝ)/60
  · left
    refine ⟨⟨8, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h9 : t ≤ (10:ℝ)/60
  · left
    refine ⟨⟨9, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h10 : t ≤ (11:ℝ)/60
  · left
    refine ⟨⟨10, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h11 : t ≤ (13:ℝ)/60
  · left
    refine ⟨⟨11, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h12 : t ≤ (15:ℝ)/60
  · left
    refine ⟨⟨12, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h13 : t ≤ (17:ℝ)/60
  · left
    refine ⟨⟨13, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h14 : t ≤ (19:ℝ)/60
  · left
    refine ⟨⟨14, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h15 : t ≤ (21:ℝ)/60
  · left
    refine ⟨⟨15, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h16 : t ≤ (23:ℝ)/60
  · left
    refine ⟨⟨16, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h17 : t ≤ (26:ℝ)/60
  · left
    refine ⟨⟨17, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h18 : t ≤ (29:ℝ)/60
  · left
    refine ⟨⟨18, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h19 : t ≤ (38:ℝ)/60
  · left
    refine ⟨⟨19, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  by_cases h20 : t ≤ (60:ℝ)/60
  · left
    refine ⟨⟨20, by omega⟩, ?_, ?_⟩
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
    · norm_num [energyMultiplierValueRaw, energyMultiplierEndpointRaw,
        energyMultiplierNode]
      linarith
  right
  norm_num [energyMultiplierEndpointRaw, energyMultiplierNode]
  linarith

/-- The time coordinate parametrizes each printed cell exactly. -/
theorem energyMultiplier_cell_time_surjective (i : Fin 21)
    (t : ℝ)
    (ht₀ : (energyMultiplierValueRaw (⟨2*i.val, by omega⟩ : Fin 43)).t ≤ t)
    (ht₁ : t ≤ (energyMultiplierValueRaw (⟨2*i.val+1, by omega⟩ : Fin 43)).t) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      (energyMultiplierCellValue i lam).t = t := by
  let j₀ : Fin 43 := ⟨2*i.val, by omega⟩
  let j₁ : Fin 43 := ⟨2*i.val+1, by omega⟩
  let a := (energyMultiplierValueRaw j₀).t
  let b := (energyMultiplierValueRaw j₁).t
  have hab : a < b := by
    fin_cases i <;> norm_num [a, b, j₀, j₁, energyMultiplierValueRaw,
      energyMultiplierEndpointRaw, energyMultiplierNode]
  have hden : 0 < b-a := sub_pos.mpr hab
  let lam := (t-a)/(b-a)
  have hlam₀ : 0 ≤ lam := div_nonneg (sub_nonneg.mpr ht₀) (le_of_lt hden)
  have hlam₁ : lam ≤ 1 := by
    apply (div_le_one hden).mpr
    dsimp only [lam, a, b] at *
    linarith
  refine ⟨lam, hlam₀, hlam₁, ?_⟩
  change (1-lam)*a+lam*b=t
  dsimp only [lam]
  field_simp [ne_of_gt hden]
  ring

end
end SpringerLean

#print axioms SpringerLean.energyMultiplier_time_covered
#print axioms SpringerLean.energyMultiplier_cell_time_surjective

