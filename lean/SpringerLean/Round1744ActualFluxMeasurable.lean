import SpringerLean.Round1741ActualFluxBoundaryPower
import Mathlib.Analysis.Calculus.FDeriv.Measurable

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual signed flux is measurable on the open source disk.
The totalized fderiv is measurable even on its exceptional set. -/
theorem actualEnergyFluxField_aestronglyMeasurable_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (beta : ℂ) :
    AEStronglyMeasurable (actualEnergyFluxField F k beta)
      (volume.restrict (ball (0 : ℂ) 1)) := by
  let μ : Measure ℂ := volume.restrict (ball (0 : ℂ) 1)
  let U := actualHarmonicPhaseField F k beta
  let t := actualHarmonicMultiplierTime F k
  have hH : AEMeasurable (actualHarmonic F) μ :=
    ((actualHarmonic_continuousOn_unitBall F hc).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet).aemeasurable
  have hy : AEMeasurable (fun z => ‖actualHarmonic F z‖) μ := hH.norm
  have hr : AEMeasurable (fun z : ℂ => ‖z‖) μ :=
    continuous_norm.measurable.aemeasurable
  have hU : AEMeasurable U μ := by
    exact Complex.continuous_im.measurable.comp_aemeasurable
      (aemeasurable_const.mul (hH.pow_const k))
  have ht : AEMeasurable t μ := by
    exact (aemeasurable_const.mul (aemeasurable_const.sub hr)).div hy
  have hchi : AEMeasurable
      (fun z => energyMultiplierChi (t z)) μ :=
    energyMultiplierChi_continuous.measurable.comp_aemeasurable ht
  have hphi : AEMeasurable
      (fun z => energyMultiplierF (t z)) μ :=
    energyMultiplierF_continuous.measurable.comp_aemeasurable ht
  have hs : AEMeasurable
      (fun z => energyMultiplierSigma (t z)) μ :=
    energyMultiplierSigma_continuous.measurable.comp_aemeasurable ht
  have hUx : AEMeasurable (fun z => (fderiv ℝ U z) (1 : ℂ)) μ :=
    (measurable_fderiv_apply_const ℝ U (1 : ℂ)).aemeasurable
  have hUy : AEMeasurable (fun z => (fderiv ℝ U z) Complex.I) μ :=
    (measurable_fderiv_apply_const ℝ U Complex.I).aemeasurable
  have hmk (a b : ℂ → ℝ) (ha : AEMeasurable a μ)
      (hb : AEMeasurable b μ) :
      AEMeasurable (fun z => Complex.mk (a z) (b z)) μ := by
    have hm : Continuous (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
      convert Complex.equivRealProdCLM.symm.continuous using 1
      ext p
      apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]
    exact hm.measurable.comp_aemeasurable (ha.prodMk hb)
  have hP : AEMeasurable (actualEnergyFluxPField F k beta) μ :=
    hmk _ _ ((hchi.mul hU).mul hUx) ((hchi.mul hU).mul hUy)
  have hzr : AEMeasurable (fun z : ℂ => z.re) μ :=
    Complex.continuous_re.measurable.aemeasurable
  have hzi : AEMeasurable (fun z : ℂ => z.im) μ :=
    Complex.continuous_im.measurable.aemeasurable
  have hB : AEMeasurable (fun z => energyMultiplierF (t z)*(U z)^2/
      ‖actualHarmonic F z‖) μ := (hphi.mul (hU.pow_const 2)).div hy
  have hR : AEMeasurable (actualEnergyFluxRField F k beta) μ :=
    hmk _ _ ((hB.mul hzr).div hr) ((hB.mul hzi).div hr)
  have hQ : AEMeasurable (fun z => (conj (actualHarmonic F z))⁻¹) μ :=
    (Complex.continuous_conj.measurable.comp_aemeasurable hH).inv
  have hQx := Complex.continuous_re.measurable.comp_aemeasurable hQ
  have hQy := Complex.continuous_im.measurable.comp_aemeasurable hQ
  have hS : AEMeasurable (actualEnergyFluxSField F k beta) μ :=
    hmk _ _ ((hs.mul (hU.pow_const 2)).mul hQx)
      ((hs.mul (hU.pow_const 2)).mul hQy)
  have hRa : AEMeasurable
      (fun z => (4*((k : ℝ)-1)) • actualEnergyFluxRField F k beta z) μ := by
    have hconst : AEMeasurable (fun _ : ℂ => 4*((k : ℝ)-1)) μ := aemeasurable_const
    convert hconst.smul hR using 1
  have hSa : AEMeasurable
      (fun z => (2*((k : ℝ)-1)) • actualEnergyFluxSField F k beta z) μ := by
    have hconst : AEMeasurable (fun _ : ℂ => 2*((k : ℝ)-1)) μ := aemeasurable_const
    convert hconst.smul hS using 1
  have hJ : AEMeasurable (actualEnergyFluxField F k beta) μ := by
    convert (hP.add hRa).sub hSa using 1
    ext z
    rfl
  exact hJ.aestronglyMeasurable

/-- This L1 majorant controls both radial collar errors. -/
theorem actualForwardDerivative_boundaryMajorant_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    IntegrableOn (fun z : ℂ =>
      1 + ‖deriv (exteriorForwardGerm F) (conj z)‖)
      (ball (0 : ℂ) 1) := by
  exact (integrableOn_const measure_ball_ne_top).add
    (exteriorForwardGerm_deriv_integrableOn F hc).norm

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_aestronglyMeasurable_unitDisk
#print axioms SpringerLean.actualForwardDerivative_boundaryMajorant_integrableOn
