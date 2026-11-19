import SpringerLean.Round275BivariateSubstitution
import SpringerLean.Round276ActualFormalInverse

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SpringerLean
open PowerSeries

theorem reciprocal_difference_quotient_identity
    {R : Type*} [CommRing R] (x y hx hy dx dy bx by' u v : R)
    (hX : hx * dx = x) (hY : hy * dy = y)
    (hDx : dx = 1 - x * bx) (hDy : dy = 1 - y * by')
    (hQ : (hy - hx) * u = hy * (1 + hx * bx) - hx * (1 + hy * by'))
    (hV : (y - x) * v = y * dx - x * dy) :
    (y - x) * (u * v) = y - x := by
  have hU : (y * dx - x * dy) * u = y - x := by
    calc
      (y * dx - x * dy) * u = ((hy - hx) * u) * dx * dy := by
        rw [← hX, ← hY]
        ring
      _ = (hy * (1 + hx * bx) - hx * (1 + hy * by')) * dx * dy := by rw [hQ]
      _ = (hy * dy) * dx - (hx * dx) * dy +
          (hx * dx) * (hy * dy) * (bx - by') := by ring
      _ = y * dx - x * dy + x * y * (bx - by') := by rw [hX, hY]
      _ = y - x := by rw [hDx, hDy]; ring
  calc
    (y - x) * (u * v) = ((y - x) * v) * u := by ring
    _ = _ := by rw [hV, hU]

/-- Simultaneous formal substitution respects the actual difference
quotient factorization. This is the common sign-sensitive inverse-kernel
identity in the convention G(w)=w-sum B_j/w^j. -/
theorem formalKernelSubst_inverse_kernel
    (f B H : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f = 0)
    (hB : PowerSeries.constantCoeff B = 0)
    (hH : PowerSeries.constantCoeff H = 0)
    (hfH : f.subst H = B)
    (hHD : H * (1 - PowerSeries.X * B) = PowerSeries.X) :
    (1 - formalKernelSubst H hH (formalFaberKernel f)) *
      (1 + formalFaberKernel B) = 1 := by
  let hs := PowerSeries.HasSubst.of_constantCoeff_zero' hH
  let M : PowerSeries ℂ →+* PowerSeries (PowerSeries ℂ) := PowerSeries.map PowerSeries.C
  let D : PowerSeries ℂ := 1 - PowerSeries.X * B
  have hphi : ((1 + PowerSeries.X * f) : PowerSeries ℂ).subst H = 1 + H * B := by
    rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs,
      PowerSeries.subst_X hs, hfH]
    simp only [← PowerSeries.coe_substAlgHom hs, map_one]
  have hX : M H * M D = PowerSeries.X := by
    rw [← map_mul, hHD]
    exact PowerSeries.map_X _
  have hY : PowerSeries.C H * PowerSeries.C D =
      (PowerSeries.C (PowerSeries.X : PowerSeries ℂ) : PowerSeries (PowerSeries ℂ)) := by
    rw [← map_mul, hHD]
  have hQ := congrArg (formalKernelSubst H hH)
    (formalFaberKernel_factorization f hf)
  try dsimp only at hQ
  simp only [map_mul, map_sub, map_one, formalKernelSubst_C,
    formalKernelSubst_X, formalKernelSubst_map_C, PowerSeries.subst_X hs,
    hphi, map_add, hfH] at hQ
  have hFB := formalFaberKernel_factorization B hB
  try dsimp only at hFB
  simp only [map_add, map_mul, map_one, PowerSeries.map_X] at hFB
  have hV :
      (PowerSeries.C (PowerSeries.X : PowerSeries ℂ) - PowerSeries.X) *
          (1 + formalFaberKernel B) =
        PowerSeries.C (PowerSeries.X : PowerSeries ℂ) * M D -
          PowerSeries.X * PowerSeries.C D := by
    dsimp only [M, D]
    simp only [map_sub, map_mul, map_one, PowerSeries.map_X]
    linear_combination -hFB
  have hmain := reciprocal_difference_quotient_identity
    (PowerSeries.X : PowerSeries (PowerSeries ℂ)) (PowerSeries.C PowerSeries.X)
    (M H) (PowerSeries.C H) (M D) (PowerSeries.C D)
    (M B) (PowerSeries.C B)
    (1 - formalKernelSubst H hH (formalFaberKernel f)) (1 + formalFaberKernel B)
    hX hY (by simp [M, D]) (by simp [D]) hQ hV
  have hnonzero : (PowerSeries.C (PowerSeries.X : PowerSeries ℂ) -
      PowerSeries.X : PowerSeries (PowerSeries ℂ)) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.coeff 1) hz
    norm_num at hc
  exact mul_left_cancel₀ hnonzero (by simpa only [mul_one] using hmain)

theorem exteriorActual_inverse_kernel_product
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    let H := schoberReciprocalSeries (schoberActualInverseSeries F)
    let hH : PowerSeries.constantCoeff H = 0 := by simp [H, schoberReciprocalSeries]
    (1 - formalKernelSubst H hH (formalFaberKernel (exteriorFormalForward F))) *
      (1 + formalFaberKernel (schoberActualInverseSeries F)) = 1 := by
  dsimp only
  apply formalKernelSubst_inverse_kernel
  · simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  · simpa only [← PowerSeries.coeff_zero_eq_constantCoeff] using
      schoberActualInverseSeries_coeff_zero F
  · exact schoberActual_forward_subst_inverse F hc
  · exact schoberActual_reciprocal_times_denominator F

end SpringerLean
