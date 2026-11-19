import SpringerLean.Round1785ActualAlignedNearPhaseCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 600000

theorem polar_relative_to_ray
    (ξ v w : ℂ) (r δ φ : ℝ)
    (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I))
    (hw : w=ξ*(r : ℂ)*Complex.exp ((φ : ℂ)*Complex.I)) :
    w=v*(r : ℂ)*Complex.exp (((φ-δ : ℝ) : ℂ)*Complex.I) := by
  have he : Complex.exp ((δ : ℂ)*Complex.I)*
      Complex.exp (((φ-δ : ℝ) : ℂ)*Complex.I)=Complex.exp ((φ : ℂ)*Complex.I) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    w=ξ*(r : ℂ)*Complex.exp ((φ : ℂ)*Complex.I) := hw
    _ = ξ*(r : ℂ)*(Complex.exp ((δ : ℂ)*Complex.I)*
          Complex.exp (((φ-δ : ℝ) : ℂ)*Complex.I)) := by rw [he]
    _ = _ := by rw [hv]; ring

theorem relative_phase_power_im_sq
    (beta ξ v w : ℂ) (k : ℕ) (hphase : (beta*v^k)^2=1)
    (r δ φ : ℝ) (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I))
    (hw : w=ξ*(r : ℂ)*Complex.exp ((φ : ℂ)*Complex.I)) :
    (beta*w^k).im^2=r^(2*k)*(Real.sin ((k : ℝ)*δ-(k : ℝ)*φ))^2 := by
  have hwp := polar_relative_to_ray ξ v w r δ φ hv hw
  have hh := phaseRay_power_im_sq beta v k hphase r (φ-δ)
  rw [←hwp] at hh
  rw [show (k : ℝ)*(φ-δ)=-((k : ℝ)*δ-(k : ℝ)*φ) by ring,
    Real.sin_neg, neg_sq] at hh
  exact hh

theorem actualHarmonicPhasePotentialDensity_relative_polar
    (F : ℂ → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (beta ξ v : ℂ) (hξ : ‖ξ‖=1) (δ : ℝ)
    (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I)) (hphase : (beta*v^k)^2=1)
    (z : ℂ) (hr : 0 < ‖actualHarmonic F z‖) :
    actualHarmonicPhasePotentialDensity F k beta z=
      ‖actualHarmonic F z‖^(2*k-2)*
        (Real.sin ((k : ℝ)*δ-(k : ℝ)*Complex.arg (conj ξ*actualHarmonic F z)))^2 := by
  have hw := unit_direction_polar ξ (actualHarmonic F z) hξ
  have hh := relative_phase_power_im_sq beta ξ v (actualHarmonic F z) k hphase
    ‖actualHarmonic F z‖ δ (Complex.arg (conj ξ*actualHarmonic F z)) hv hw
  have hpow : ‖actualHarmonic F z‖^(2*k)=‖actualHarmonic F z‖^(2*k-2)*‖actualHarmonic F z‖^2 := by
    rw [←pow_add]
    congr 1
    omega
  unfold actualHarmonicPhasePotentialDensity actualHarmonicPhaseField
  rw [hh, hpow]
  field_simp [hr.ne']

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhasePotentialDensity_relative_polar
