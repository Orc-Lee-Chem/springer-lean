import SpringerLean.Round1626EnergySplineCellDerivatives

namespace SpringerLean

/-- A ramp has reached its constant tail after the final knot. -/
theorem energyMultiplierRamp_on_tail
    (i : Fin 21) (t : ℝ)
    (ht : energyMultiplierKnotTime (21 : Fin 22) ≤ t) :
    energyMultiplierRamp
      (energyMultiplierKnotTime i.castSucc)
      (energyMultiplierKnotTime i.succ) t =
        energyMultiplierKnotTime i.succ -
          energyMultiplierKnotTime i.castSucc := by
  have hfinal : energyMultiplierKnotTime i.succ ≤
      energyMultiplierKnotTime (21 : Fin 22) := by
    apply energyMultiplierKnotTime_strictMono.monotone
    apply Fin.le_iff_val_le_val.mpr
    simp
  have hcell : energyMultiplierKnotTime i.castSucc ≤
      energyMultiplierKnotTime i.succ :=
    le_of_lt (energyMultiplierKnotTime_strictMono Fin.castSucc_lt_succ)
  exact energyMultiplierRamp_after hcell (hfinal.trans ht)

/-- A generic ramp spline is constant after the last knot, with value
given by the final nodal increment. -/
theorem energyMultiplierSpline_generic_tail
    (slope : Fin 21 → ℝ) (node : ℕ → ℝ)
    (hincrement : ∀ i : Fin 21,
      slope i *
        (energyMultiplierKnotTime i.succ -
          energyMultiplierKnotTime i.castSucc) =
        node (i.val+1)-node i.val)
    (t : ℝ) (ht : energyMultiplierKnotTime (21 : Fin 22) ≤ t) :
    (∑ i : Fin 21,
      slope i * energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t) =
      node 21-node 0 := by
  calc
    (∑ i : Fin 21,
      slope i * energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t) =
      ∑ i : Fin 21,
        slope i *
          (energyMultiplierKnotTime i.succ -
            energyMultiplierKnotTime i.castSucc) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [energyMultiplierRamp_on_tail i t ht]
    _ = ∑ i : Fin 21, (node (i.val+1)-node i.val) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hincrement i
    _ = ∑ i ∈ Finset.range 21, (node (i+1)-node i) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => node (i+1)-node i) 21
    _ = node 21-node 0 := Finset.sum_range_sub node 21

end SpringerLean

#print axioms SpringerLean.energyMultiplierRamp_on_tail
#print axioms SpringerLean.energyMultiplierSpline_generic_tail
