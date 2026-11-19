import SpringerLean.Round1916NormalizedRadialMoment
import SpringerLean.Round1869SlitRadialTrace

open MeasureTheory Set
open scoped ComplexConjugate

namespace SpringerLean

/-- The cosine law is exactly the normalized actual radial trace of the
unit slit map. -/
theorem normalizedCosineMoment_eq_slit_constant
    (p : ℝ) (hp : 0 < p) :
    normalizedCosineMoment p =
      slitRadialMomentConstant p / (2 : ℝ) ^ p := by
  have hslit := actualBoundaryRadialMoment_slitMap_one p hp
  have hmodel : normalizedCosineMoment p =
      normalizedActualRadialMoment (slitMap 1) p := by
    rw [normalizedActualRadialMoment_eq_integral,
      normalizedCosineMoment, circleAverage_eq_polar_setIntegral]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with θ
    rw [actualExteriorRadialTrace_slitMap_one]
    have hpolar : (Complex.polarCoord.symm (1, θ)).re = Real.cos θ := by
      simp only [Complex.polarCoord_symm_apply, one_mul,
        Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hpolar]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h : 2 * |Real.cos θ| / 2 = |Real.cos θ| := by ring
    rw [h]
  rw [hmodel, normalizedActualRadialMoment, hslit]

end SpringerLean

#print axioms SpringerLean.normalizedCosineMoment_eq_slit_constant
