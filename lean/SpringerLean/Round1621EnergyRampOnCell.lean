import SpringerLean.Round1620EnergySplineCellIncrements

namespace SpringerLean

/-- On one open printed cell, each ramp is constant, linear, or zero
according to its position relative to that cell. -/
theorem energyMultiplierRamp_on_cell
    (i j : Fin 21) (t : ℝ)
    (hleft : energyMultiplierKnotTime j.castSucc ≤ t)
    (hright : t ≤ energyMultiplierKnotTime j.succ) :
    energyMultiplierRamp
      (energyMultiplierKnotTime i.castSucc)
      (energyMultiplierKnotTime i.succ) t =
        if i < j then
          energyMultiplierKnotTime i.succ -
            energyMultiplierKnotTime i.castSucc
        else if i = j then
          t - energyMultiplierKnotTime j.castSucc
        else 0 := by
  rcases lt_trichotomy i j with hij | heq | hji
  · have hbi : energyMultiplierKnotTime i.succ ≤
        energyMultiplierKnotTime j.castSucc := by
      apply energyMultiplierKnotTime_strictMono.monotone
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hai : energyMultiplierKnotTime i.castSucc ≤
        energyMultiplierKnotTime i.succ :=
      le_of_lt (energyMultiplierKnotTime_strictMono Fin.castSucc_lt_succ)
    rw [energyMultiplierRamp_after hai (hbi.trans hleft)]
    simp [hij]
  · subst j
    rw [energyMultiplierRamp_inside hleft hright]
    simp
  · have haj : energyMultiplierKnotTime j.succ ≤
        energyMultiplierKnotTime i.castSucc := by
      apply energyMultiplierKnotTime_strictMono.monotone
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hai : energyMultiplierKnotTime i.castSucc ≤
        energyMultiplierKnotTime i.succ :=
      le_of_lt (energyMultiplierKnotTime_strictMono Fin.castSucc_lt_succ)
    rw [energyMultiplierRamp_before (hright.trans haj) hai]
    have hnot : ¬ i < j := not_lt.mpr (le_of_lt hji)
    have hne : i ≠ j := ne_of_gt hji
    simp [hnot, hne]

end SpringerLean

#print axioms SpringerLean.energyMultiplierRamp_on_cell
