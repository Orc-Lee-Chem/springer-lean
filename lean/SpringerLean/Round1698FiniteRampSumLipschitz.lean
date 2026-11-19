import SpringerLean.Round1697EnergyRampLipschitz

namespace SpringerLean

/-- A finite linear combination of the physical spline ramps is globally
Lipschitz. The constant is explicit, but no numerical slope bound is needed. -/
theorem finiteRampSum_lipschitz
    {ι : Type*} [Fintype ι] (c a b : ι → ℝ) :
    LipschitzWith
      (∑ i : ι, (⟨2 * |c i|, by positivity⟩ : NNReal))
      (fun t : ℝ => ∑ i : ι, c i * energyMultiplierRamp (a i) (b i) t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  calc
    |(∑ i : ι, c i * energyMultiplierRamp (a i) (b i) x) -
        (∑ i : ι, c i * energyMultiplierRamp (a i) (b i) y)| =
      |∑ i : ι, (c i * energyMultiplierRamp (a i) (b i) x -
        c i * energyMultiplierRamp (a i) (b i) y)| := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i : ι, |c i * energyMultiplierRamp (a i) (b i) x -
        c i * energyMultiplierRamp (a i) (b i) y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, (2 * |c i|) * |x - y| := by
          apply Finset.sum_le_sum
          intro i hi
          have hr := (energyMultiplierRamp_lipschitz (a i) (b i)).dist_le_mul x y
          simp only [Real.dist_eq, NNReal.coe_ofNat] at hr
          calc
            |c i * energyMultiplierRamp (a i) (b i) x -
                c i * energyMultiplierRamp (a i) (b i) y| =
              |c i| * |energyMultiplierRamp (a i) (b i) x -
                energyMultiplierRamp (a i) (b i) y| := by
                  rw [← mul_sub, abs_mul]
            _ ≤ |c i| * (2 * |x - y|) :=
              mul_le_mul_of_nonneg_left hr (abs_nonneg _)
            _ = (2 * |c i|) * |x - y| := by ring
    _ = (↑(∑ i : ι, (⟨2 * |c i|, by positivity⟩ : NNReal)) : ℝ) *
        |x - y| := by
          rw [← Finset.sum_mul]
          congr 1
          symm
          exact NNReal.coe_sum Finset.univ
            (fun i : ι => (⟨2 * |c i|, by positivity⟩ : NNReal))

theorem energyMultiplierChi_lipschitz :
    LipschitzWith
      (∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).cp : ℝ)|,
          by positivity⟩ : NNReal))
      energyMultiplierChi := by
  convert finiteRampSum_lipschitz
      (fun i : Fin 21 => ((energyMultiplierEndpointRaw (2 * i.val)).cp : ℝ))
      (fun i => energyMultiplierKnotTime i.castSucc)
      (fun i => energyMultiplierKnotTime i.succ) using 1
  funext t
  rfl

theorem energyMultiplierF_lipschitz :
    LipschitzWith
      (∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).fp : ℝ)|,
          by positivity⟩ : NNReal))
      energyMultiplierF := by
  convert finiteRampSum_lipschitz
      (fun i : Fin 21 => ((energyMultiplierEndpointRaw (2 * i.val)).fp : ℝ))
      (fun i => energyMultiplierKnotTime i.castSucc)
      (fun i => energyMultiplierKnotTime i.succ) using 1
  funext t
  rfl

theorem energyMultiplierSigma_lipschitz :
    LipschitzWith
      (∑ i : Fin 21,
        (⟨2 * |((energyMultiplierEndpointRaw (2 * i.val)).sp : ℝ)|,
          by positivity⟩ : NNReal))
      energyMultiplierSigma := by
  convert finiteRampSum_lipschitz
      (fun i : Fin 21 => ((energyMultiplierEndpointRaw (2 * i.val)).sp : ℝ))
      (fun i => energyMultiplierKnotTime i.castSucc)
      (fun i => energyMultiplierKnotTime i.succ) using 1
  funext t
  rfl

end SpringerLean

#print axioms SpringerLean.finiteRampSum_lipschitz
#print axioms SpringerLean.energyMultiplierChi_lipschitz
#print axioms SpringerLean.energyMultiplierF_lipschitz
#print axioms SpringerLean.energyMultiplierSigma_lipschitz
