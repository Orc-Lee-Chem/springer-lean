import SpringerLean.Round1617ActualLocalAffineRadialFlux

namespace SpringerLean
noncomputable section

/-- The 22 physical time knots of the printed energy multiplier. -/
def energyMultiplierKnotTime (i : Fin 22) : ℝ :=
  (energyMultiplierEndpointRaw (2*i.val)).t

theorem energyMultiplierKnotTime_strictMono :
    StrictMono energyMultiplierKnotTime := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;>
    norm_num [energyMultiplierKnotTime, energyMultiplierEndpointRaw,
      energyMultiplierNode]

/-- A finite-cell ramp, linear on its cell and constant afterward. -/
def energyMultiplierRamp (a b t : ℝ) : ℝ :=
  max 0 (t-a) - max 0 (t-b)

theorem energyMultiplierRamp_continuous (a b : ℝ) :
    Continuous (energyMultiplierRamp a b) := by
  unfold energyMultiplierRamp
  fun_prop

attribute [fun_prop] energyMultiplierRamp_continuous

/-- The global continuous piecewise-affine chi multiplier. -/
def energyMultiplierChi (t : ℝ) : ℝ :=
  ∑ i : Fin 21,
    ((energyMultiplierEndpointRaw (2*i.val)).cp : ℝ) *
      energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t

/-- The global continuous piecewise-affine radial multiplier. -/
def energyMultiplierF (t : ℝ) : ℝ :=
  ∑ i : Fin 21,
    ((energyMultiplierEndpointRaw (2*i.val)).fp : ℝ) *
      energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t

/-- The global continuous piecewise-affine drift multiplier. -/
def energyMultiplierSigma (t : ℝ) : ℝ :=
  ∑ i : Fin 21,
    ((energyMultiplierEndpointRaw (2*i.val)).sp : ℝ) *
      energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t

theorem energyMultiplierChi_continuous : Continuous energyMultiplierChi := by
  unfold energyMultiplierChi
  fun_prop

theorem energyMultiplierF_continuous : Continuous energyMultiplierF := by
  unfold energyMultiplierF
  fun_prop

theorem energyMultiplierSigma_continuous : Continuous energyMultiplierSigma := by
  unfold energyMultiplierSigma
  fun_prop

end
end SpringerLean

#print axioms SpringerLean.energyMultiplierKnotTime_strictMono
#print axioms SpringerLean.energyMultiplierChi_continuous
#print axioms SpringerLean.energyMultiplierF_continuous
#print axioms SpringerLean.energyMultiplierSigma_continuous
