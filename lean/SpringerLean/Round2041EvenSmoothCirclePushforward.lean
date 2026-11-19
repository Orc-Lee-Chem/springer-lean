import SpringerLean.Round2040EvenBLPTangentExtension
import SpringerLean.Round1960CenteredAngleAverage

open MeasureTheory Set

namespace SpringerLean


theorem polar_radius_as_unit (s θ : ℝ) :
    Complex.polarCoord.symm (s,θ) =
      (s:ℂ)*Complex.polarCoord.symm (1,θ) := by
  simp [Complex.polarCoord_symm_apply]

theorem polar_radius_pow (r : ℝ) (k : ℕ) (θ : ℝ) :
    (Complex.polarCoord.symm (r⁻¹,θ))^k =
      Complex.polarCoord.symm ((r^k)⁻¹,(k:ℝ)*θ) := by
  calc
    (Complex.polarCoord.symm (r⁻¹,θ))^k =
        ((r⁻¹:ℂ)*Complex.polarCoord.symm (1,θ))^k := by
      rw [polar_radius_as_unit]
      simp
    _ = ((r^k)⁻¹:ℂ)*Complex.polarCoord.symm (1,(k:ℝ)*θ) := by
      rw [mul_pow, unitPolar_pow, inv_pow]
    _ = Complex.polarCoord.symm ((r^k)⁻¹,(k:ℝ)*θ) :=
      by simpa using
        (polar_radius_as_unit ((r^k)⁻¹) ((k:ℝ)*θ)).symm

theorem evenPowerQuotient_smooth_circle_power
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    evenExteriorPowerQuotient F k
      (Complex.polarCoord.symm ((r^k)⁻¹,(k:ℝ)*θ)) =
      (F (Complex.polarCoord.symm (r⁻¹,θ)))^k := by
  let z : ℂ := Complex.polarCoord.symm (r⁻¹,θ)
  have hz : z ∈ exteriorDisk := by
    change 1 < ‖z‖
    dsimp [z]
    rw [Complex.norm_polarCoord_symm, abs_of_pos (inv_pos.mpr hr0)]
    exact (one_lt_inv₀ hr0).2 hr1
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  rw [← polar_radius_pow r k θ]
  exact evenExteriorPowerQuotient_comp_pow F k hk hcov z hz

theorem evenPowerQuotient_smooth_circle_integral_pushforward
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (φ : ℂ → ℝ) (hφ : Continuous φ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      φ ((F (Complex.polarCoord.symm (r⁻¹,θ)))^k)) =
    ∫ θ in Ioo (-Real.pi) Real.pi,
      φ (evenExteriorPowerQuotient F k
        (Complex.polarCoord.symm ((r^k)⁻¹,θ))) := by
  let G := evenExteriorPowerQuotient F k
  let s : ℝ := (r^k)⁻¹
  let f : ℝ → ℝ := fun θ => φ (G (Complex.polarCoord.symm (s,θ)))
  have hrk0 : 0 < r^k := pow_pos hr0 k
  have hrk1 : r^k < 1 := pow_lt_one₀ hr0.le hr1 (by omega)
  have hs : 1 < s := (one_lt_inv₀ hrk0).2 hrk1
  have hpolar : Continuous (fun θ : ℝ => Complex.polarCoord.symm (s,θ)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hmem (θ : ℝ) : Complex.polarCoord.symm (s,θ) ∈ exteriorDisk := by
    change 1 < ‖Complex.polarCoord.symm (s,θ)‖
    rw [Complex.norm_polarCoord_symm, abs_of_pos (by linarith : 0 < s)]
    exact hs
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  have hGcont : Continuous (fun θ : ℝ => G (Complex.polarCoord.symm (s,θ))) :=
    hG.1.continuousOn.comp_continuous hpolar hmem
  have hfcont : Continuous f := hφ.comp hGcont
  have hfperiod : Function.Periodic f (2*Real.pi) := by
    intro θ
    have hp : (Complex.polarCoord.symm (s,θ+2*Real.pi):ℂ) =
        Complex.polarCoord.symm (s,θ) := by
      calc
        Complex.polarCoord.symm (s,θ+2*Real.pi) =
            (s:ℂ)*Complex.polarCoord.symm (1,θ+2*Real.pi) :=
          polar_radius_as_unit _ _
        _ = (s:ℂ)*Complex.polarCoord.symm (1,θ) := by
          exact congrArg (fun z : ℂ => (s:ℂ)*z) (unitPolar_periodic θ)
        _ = Complex.polarCoord.symm (s,θ) :=
          (polar_radius_as_unit _ _).symm
    exact congrArg (fun z : ℂ => φ (G z)) hp
  have hperiodic := periodic_setIntegral_comp_nat_mul_centered
    f hfperiod hfcont k hk
  have hleft : (∫ θ in Ioo (-Real.pi) Real.pi,
      f ((k:ℝ)*θ)) =
      ∫ θ in Ioo (-Real.pi) Real.pi,
        φ ((F (Complex.polarCoord.symm (r⁻¹,θ)))^k) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with θ
    exact congrArg φ
      (evenPowerQuotient_smooth_circle_power
        F K k hk hF hK hImage r hr0 hr1 θ)
  exact hleft.symm.trans hperiodic

end SpringerLean
