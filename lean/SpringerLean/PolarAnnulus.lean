import SpringerLean.AreaUpper
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace SpringerLean

/-- On the positive-radius polar chart, membership in the actual annulus
depends only on the radial coordinate. -/
theorem exteriorAnnulus_polar_iff
    (r R : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ exteriorAnnulus r R ↔
      r < p.1 ∧ p.1 < R := by
  have hp0 : 0 < p.1 := by
    change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi at hp
    exact hp.1
  simp only [exteriorAnnulus, Set.mem_ofPred_eq,
    Complex.norm_polarCoord_symm, abs_of_pos hp0]

/-- The polar chart's angular point is exactly the same Fourier circle point
used in the verified fixed-circle Bessel estimate. -/
theorem exteriorCirclePoint_eq_polarCoord_symm (ρ θ : ℝ) :
    exteriorCirclePoint ρ (θ : AddCircle (2 * Real.pi)) =
      Complex.polarCoord.symm (ρ, θ) := by
  rw [Complex.polarCoord_symm_apply]
  unfold exteriorCirclePoint
  rw [fourier_coe_apply]
  rw [← Complex.exp_ofReal_mul_I]
  congr 1
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  push_cast
  ring

/-- The overlap of the positive polar chart with an exterior annulus is the
product of the radial and angular open intervals. -/
theorem exteriorAnnulus_polar_preimage_inter
    {r R : ℝ} (hr : 0 < r) :
    Complex.polarCoord.target ∩
      (fun p : ℝ × ℝ => Complex.polarCoord.symm p) ⁻¹'
        exteriorAnnulus r R =
      Set.Ioo r R ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  ext p
  constructor
  · rintro ⟨hp, hA⟩
    have hpangle : p.2 ∈ Set.Ioo (-Real.pi) Real.pi := by
      change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi at hp
      exact hp.2
    exact ⟨(exteriorAnnulus_polar_iff r R p hp).mp hA, hpangle⟩
  · intro hp
    have hptarget : p ∈ Complex.polarCoord.target := by
      change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
      exact ⟨lt_trans hr hp.1.1, hp.2⟩
    exact ⟨hptarget, (exteriorAnnulus_polar_iff r R p hptarget).mpr hp.1⟩

end SpringerLean
