import SpringerLean.Round1623FiniteSplineTelescoping

namespace SpringerLean

/-- A finite ramp spline equals its nodal value plus the active affine
slope on every cell. The proof is a generic telescoping calculation. -/
theorem energyMultiplierSpline_generic_on_cell
    (slope : Fin 21 → ℝ) (node : ℕ → ℝ)
    (hincrement : ∀ i : Fin 21,
      slope i *
        (energyMultiplierKnotTime i.succ -
          energyMultiplierKnotTime i.castSucc) =
        node (i.val+1)-node i.val)
    (j : Fin 21) (t : ℝ)
    (hleft : energyMultiplierKnotTime j.castSucc ≤ t)
    (hright : t ≤ energyMultiplierKnotTime j.succ) :
    (∑ i : Fin 21,
      slope i * energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t) =
      node j.val-node 0+
        slope j*(t-energyMultiplierKnotTime j.castSucc) := by
  let c : ℝ := slope j*(t-energyMultiplierKnotTime j.castSucc)
  have hterm (i : Fin 21) :
      slope i * energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t =
      if i.val < j.val then node (i.val+1)-node i.val
      else if i.val = j.val then c else 0 := by
    rw [energyMultiplierRamp_on_cell i j t hleft hright]
    rcases lt_trichotomy i j with hij | heq | hji
    · have hv : i.val < j.val := Fin.lt_iff_val_lt_val.mp hij
      simp [hij, hv, hincrement i]
    · subst j
      simp [c]
    · have hv : ¬ i.val < j.val :=
        not_lt.mpr (Fin.le_iff_val_le_val.mp (le_of_lt hji))
      have hne : i.val ≠ j.val := by omega
      have hn : ¬ i < j := not_lt.mpr (le_of_lt hji)
      have hfin : i ≠ j := ne_of_gt hji
      simp [hv, hne, hn, hfin]
  calc
    (∑ i : Fin 21,
      slope i * energyMultiplierRamp
        (energyMultiplierKnotTime i.castSucc)
        (energyMultiplierKnotTime i.succ) t) =
      ∑ i : Fin 21,
        if i.val < j.val then node (i.val+1)-node i.val
        else if i.val = j.val then c else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = ∑ i ∈ Finset.range 21,
        if i < j.val then node (i+1)-node i
        else if i = j.val then c else 0 :=
          Fin.sum_univ_eq_sum_range
            (fun i : ℕ =>
              if i < j.val then node (i+1)-node i
              else if i = j.val then c else 0) 21
    _ = _ := by
      rw [sum_range_piecewise_telescopes node j.val 21 c j.isLt]

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_generic_on_cell
