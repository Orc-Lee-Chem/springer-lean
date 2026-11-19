import SpringerLean.Round1585EnergySegmentConvex

namespace SpringerLean
set_option maxHeartbeats 2000000
noncomputable section

/-- The value fields of one printed endpoint, without its one-sided slope. -/
def energyMultiplierValueRaw (j : Fin 43) : EnergyMultiplierValue :=
  let v := energyMultiplierEndpointRaw j
  ⟨v.t, v.chi, v.f, v.sigma⟩

/-- The raw endpoint theorem expressed in the affine-cell notation. -/
theorem energyMultiplier_allK_endpoint_quadratic_value
    {k : ℕ} (hk : 751 ≤ k) (j : Fin 43)
    {s : ℝ} (hs : 0 ≤ s) :
    let v := energyMultiplierEndpointRaw j
    signedEnergyQuadratic
      (energyMultiplierA (1/(k:ℝ)) v.fp v.sp (energyMultiplierValueRaw j))
      (energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) v.cp v.fp v.sp (energyMultiplierValueRaw j))
      (energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) v.cp
        (energyMultiplierValueRaw j)) s ≤ 25/16 := by
  have h := energyMultiplier_allK_endpoint_quadratic hk j hs
  dsimp only at h ⊢
  have hkpos : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkm1 : (k:ℝ)-1 ≠ 0 := by
    have : (751:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  convert h using 1 <;>
    dsimp [energyMultiplierA, energyMultiplierB, energyMultiplierD,
      energyMultiplierValueRaw, coeffQ, coeffP] <;>
    simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The two one-sided printed cases belonging to each finite cell have
the same three slopes. This is a finite identity about the input table. -/
theorem energyMultiplier_cell_slopes_agree (i : Fin 21) :
    let v₀ := energyMultiplierEndpointRaw (⟨2*i.val, by omega⟩ : Fin 43)
    let v₁ := energyMultiplierEndpointRaw (⟨2*i.val+1, by omega⟩ : Fin 43)
    v₀.cp = v₁.cp ∧ v₀.fp = v₁.fp ∧ v₀.sp = v₁.sp := by
  fin_cases i <;>
    norm_num [energyMultiplierEndpointRaw,energyMultiplierNode,
      energyMultiplierSlope]

/-- Interpolation of the value fields on one printed finite cell. -/
def energyMultiplierCellValue (i : Fin 21) (lam : ℝ) :
    EnergyMultiplierValue :=
  let v₀ := energyMultiplierValueRaw (⟨2*i.val, by omega⟩ : Fin 43)
  let v₁ := energyMultiplierValueRaw (⟨2*i.val+1, by omega⟩ : Fin 43)
  ⟨(1-lam)*v₀.t+lam*v₁.t,
   (1-lam)*v₀.chi+lam*v₁.chi,
   (1-lam)*v₀.f+lam*v₁.f,
   (1-lam)*v₀.sigma+lam*v₁.sigma⟩

/-- Every finite multiplier cell obeys the original quadratic bound,
for every interpolation parameter and every order k ≥ 751. -/
theorem energyMultiplier_allK_finiteCell_quadratic
    {k : ℕ} (hk : 751 ≤ k) (i : Fin 21)
    {lam s : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (hs : 0 ≤ s) :
    let j₀ : Fin 43 := ⟨2*i.val, by omega⟩
    let r₀ := energyMultiplierEndpointRaw j₀
    signedEnergyQuadratic
      (energyMultiplierA (1/(k:ℝ)) r₀.fp r₀.sp (energyMultiplierCellValue i lam))
      (energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) r₀.cp r₀.fp r₀.sp
        (energyMultiplierCellValue i lam))
      (energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) r₀.cp
        (energyMultiplierCellValue i lam)) s ≤ 25/16 := by
  let j₀ : Fin 43 := ⟨2*i.val, by omega⟩
  let j₁ : Fin 43 := ⟨2*i.val+1, by omega⟩
  let r₀ := energyMultiplierEndpointRaw j₀
  let r₁ := energyMultiplierEndpointRaw j₁
  let v₀ := energyMultiplierValueRaw j₀
  let v₁ := energyMultiplierValueRaw j₁
  have hslopes := energyMultiplier_cell_slopes_agree i
  change r₀.cp = r₁.cp ∧ r₀.fp = r₁.fp ∧ r₀.sp = r₁.sp at hslopes
  obtain ⟨hcp,hfp,hsp⟩ := hslopes
  have h₀ := energyMultiplier_allK_endpoint_quadratic_value hk j₀ hs
  have h₁ := energyMultiplier_allK_endpoint_quadratic_value hk j₁ hs
  dsimp only at h₀ h₁
  rw [← hcp, ← hfp, ← hsp] at h₁
  have hkR : (1:ℝ) < k := by
    have : (751:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have ha : 0 ≤ 1/(k:ℝ) := by positivity
  have hg : 0 ≤ 1/((k:ℝ)-1) := by positivity
  have hseg := energyMultiplierQuadratic_segment_le
    (v₀ := v₀) (v₁ := v₁) (v := energyMultiplierCellValue i lam)
    (lam := lam) (alpha := 1/(k:ℝ))
    (gamma := 1/((k:ℝ)-1)) (K := (k:ℝ))
    (b := (k:ℝ)/(4*((k:ℝ)-1)))
    (cp := r₀.cp) (fp := r₀.fp) (sp := r₀.sp) (s := s)
    hlam₀ hlam₁ ha hg hs
    (by rfl) (by rfl) (by rfl) (by rfl)
  have h₀w := mul_le_mul_of_nonneg_left h₀ (by linarith : 0 ≤ 1-lam)
  have h₁w := mul_le_mul_of_nonneg_left h₁ hlam₀
  dsimp only [energyMultiplierCellValue] at hseg ⊢
  nlinarith

/-- Beyond the last printed knot all three multipliers are constant. -/
def energyMultiplierTailValue (t : ℝ) : EnergyMultiplierValue :=
  let r := energyMultiplierEndpointRaw 42
  ⟨t, r.chi, r.f, r.sigma⟩

theorem energyMultiplier_allK_tail_quadratic
    {k : ℕ} (hk : 751 ≤ k) {s t : ℝ} (hs : 0 ≤ s) :
    let r := energyMultiplierEndpointRaw 42
    signedEnergyQuadratic
      (energyMultiplierA (1/(k:ℝ)) r.fp r.sp (energyMultiplierTailValue t))
      (energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) r.cp r.fp r.sp
        (energyMultiplierTailValue t))
      (energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) r.cp
        (energyMultiplierTailValue t)) s ≤ 25/16 := by
  have h := energyMultiplier_allK_endpoint_quadratic_value hk
    (⟨42, by omega⟩ : Fin 43) hs
  norm_num [energyMultiplierEndpointRaw, energyMultiplierNode,
    energyMultiplierTailValue, energyMultiplierValueRaw,
    energyMultiplierA, energyMultiplierB, energyMultiplierD,
    coeffQ, coeffP] at h ⊢
  exact h

end
end SpringerLean

#print axioms SpringerLean.energyMultiplier_allK_endpoint_quadratic_value
#print axioms SpringerLean.energyMultiplier_cell_slopes_agree
#print axioms SpringerLean.energyMultiplier_allK_finiteCell_quadratic
#print axioms SpringerLean.energyMultiplier_allK_tail_quadratic
