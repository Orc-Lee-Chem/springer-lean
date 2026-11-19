import SpringerLean.Round1618EnergyMultiplierSpline

namespace SpringerLean

theorem energyMultiplierRamp_before
    {a b t : ℝ} (ht : t ≤ a) (hab : a ≤ b) :
    energyMultiplierRamp a b t = 0 := by
  have hta : t-a ≤ 0 := sub_nonpos.mpr ht
  have htb : t-b ≤ 0 := by linarith
  simp [energyMultiplierRamp, max_eq_left hta, max_eq_left htb]

theorem energyMultiplierRamp_inside
    {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    energyMultiplierRamp a b t = t-a := by
  have hta : 0 ≤ t-a := sub_nonneg.mpr hat
  have htb' : t-b ≤ 0 := sub_nonpos.mpr htb
  simp [energyMultiplierRamp, max_eq_right hta, max_eq_left htb']

theorem energyMultiplierRamp_after
    {a b t : ℝ} (hab : a ≤ b) (hbt : b ≤ t) :
    energyMultiplierRamp a b t = b-a := by
  have hta : 0 ≤ t-a := by linarith
  have htb : 0 ≤ t-b := sub_nonneg.mpr hbt
  simp [energyMultiplierRamp, max_eq_right hta, max_eq_right htb]

theorem energyMultiplierKnotTime_zero :
    energyMultiplierKnotTime (0 : Fin 22) = 0 := by
  norm_num [energyMultiplierKnotTime, energyMultiplierEndpointRaw,
    energyMultiplierNode]

theorem energyMultiplierKnotTime_nonneg (i : Fin 22) :
    0 ≤ energyMultiplierKnotTime i := by
  rw [← energyMultiplierKnotTime_zero]
  exact (energyMultiplierKnotTime_strictMono.monotone (Fin.zero_le i))

theorem energyMultiplierRamp_cell_zero {t : ℝ} (ht : t ≤ 0)
    (i : Fin 21) :
    energyMultiplierRamp
      (energyMultiplierKnotTime i.castSucc)
      (energyMultiplierKnotTime i.succ) t = 0 := by
  apply energyMultiplierRamp_before
  · exact ht.trans (energyMultiplierKnotTime_nonneg i.castSucc)
  · exact le_of_lt
      (energyMultiplierKnotTime_strictMono Fin.castSucc_lt_succ)

theorem energyMultiplierChi_before_zero {t : ℝ} (ht : t ≤ 0) :
    energyMultiplierChi t = 0 := by
  unfold energyMultiplierChi
  apply Finset.sum_eq_zero
  intro i hi
  rw [energyMultiplierRamp_cell_zero ht i, mul_zero]

theorem energyMultiplierF_before_zero {t : ℝ} (ht : t ≤ 0) :
    energyMultiplierF t = 0 := by
  unfold energyMultiplierF
  apply Finset.sum_eq_zero
  intro i hi
  rw [energyMultiplierRamp_cell_zero ht i, mul_zero]

theorem energyMultiplierSigma_before_zero {t : ℝ} (ht : t ≤ 0) :
    energyMultiplierSigma t = 0 := by
  unfold energyMultiplierSigma
  apply Finset.sum_eq_zero
  intro i hi
  rw [energyMultiplierRamp_cell_zero ht i, mul_zero]

end SpringerLean

#print axioms SpringerLean.energyMultiplierRamp_before
#print axioms SpringerLean.energyMultiplierRamp_inside
#print axioms SpringerLean.energyMultiplierRamp_after
#print axioms SpringerLean.energyMultiplierChi_before_zero
#print axioms SpringerLean.energyMultiplierF_before_zero
#print axioms SpringerLean.energyMultiplierSigma_before_zero
