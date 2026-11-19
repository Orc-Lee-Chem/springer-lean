import SpringerLean.Round1493AssignedAxisCaps

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 160000

/-- On the forward half of one unit axis, any second unit axis whose
endpoint lies in the opposite half has projection bounded by the
transverse coordinate. This is the geometric bridge for the second
endpoint's full boundary cap. -/
theorem oppositeAxis_projection_le_transverse
    (a P w : ℂ) (ha : ‖a‖=1) (hP : 0<‖P‖)
    (hneg : (conj a*P).re ≤ 0)
    (hforward : 0 ≤ (conj a*w).re) :
    (conj (P/(‖P‖:ℂ))*w).re ≤ |(conj a*w).im| := by
  let u : ℂ := conj a*w
  let v : ℂ := conj a*P
  have hunit : a*conj a=1 := by
    simp [Complex.mul_conj,Complex.normSq_eq_norm_sq,ha]
  have hnormv : ‖v‖=‖P‖ := by
    dsimp [v]
    rw [norm_mul,Complex.norm_conj,ha,one_mul]
  have hcomplex : conj (P/(‖P‖:ℂ))*w=(conj v*u)/(‖P‖:ℂ) := by
    dsimp [u,v]
    rw [map_div₀,Complex.conj_ofReal]
    have hmul : (a*conj P)*(conj a*w)=conj P*w := by
      calc
        _ = (a*conj a)*(conj P*w) := by ring
        _ = conj P*w := by rw [hunit,one_mul]
    calc
      (conj P/(‖P‖:ℂ))*w=(conj P*w)/(‖P‖:ℂ) := by ring
      _ = (conj (conj a*P)*(conj a*w))/(‖P‖:ℂ) := by
        rw [map_mul,Complex.conj_conj,hmul]
  have hcoord : (conj (P/(‖P‖:ℂ))*w).re =
      (v.re*u.re+v.im*u.im)/‖P‖ := by
    rw [hcomplex]
    rw [div_eq_mul_inv,←Complex.ofReal_inv]
    simp [Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hvre : v.re ≤ 0 := hneg
  have hure : 0 ≤ u.re := hforward
  have hvim : |v.im| ≤ ‖P‖ := by
    rw [←hnormv]
    exact Complex.abs_im_le_norm v
  have hprod : v.re*u.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hvre hure
  have him : v.im*u.im ≤ |v.im| * |u.im| := by
    calc
      v.im*u.im ≤ |v.im * u.im| := le_abs_self _
      _ = |v.im| * |u.im| := abs_mul _ _
  rw [hcoord]
  apply (div_le_iff₀ hP).2
  nlinarith [mul_le_mul_of_nonneg_right hvim (abs_nonneg u.im)]

end SpringerLean

#print axioms SpringerLean.oppositeAxis_projection_le_transverse
