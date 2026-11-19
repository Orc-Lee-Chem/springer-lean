import SpringerLean.Round1905KernelSecantBound
import SpringerLean.Round1887InterpolationPowerAMGM

open scoped Topology

namespace SpringerLean

theorem interpolationPowerTest_hasDerivAt
    {a θ t : ℝ} (ht : 0 < t) (ha : a ≠ 0) (ha2 : a + 2 ≠ 0) :
    HasDerivAt (interpolationPowerTest a θ)
      ((a + 2 * θ) * t ^ (a + 2 * θ - 1) -
        (a + 2 * θ) * (1 - θ) * t ^ (a - 1) -
        (a + 2 * θ) * θ * t ^ (a + 1)) t := by
  let p := a + 2 * θ
  have h1 := Real.hasDerivAt_rpow_const (p := p) (Or.inl ht.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
  have h3 := Real.hasDerivAt_rpow_const (p := a + 2) (Or.inl ht.ne')
  have h := (h1.sub (h2.const_mul (p * (1 - θ) / a))).sub
    (h3.const_mul (p * θ / (a + 2)))
  change HasDerivAt
    (((fun x : ℝ => x ^ p) - fun x => (p * (1 - θ) / a) * x ^ a) -
      fun x => (p * θ / (a + 2)) * x ^ (a + 2))
    (p * t ^ (p - 1) - p * (1 - θ) * t ^ (a - 1) -
      p * θ * t ^ (a + 1)) t
  convert h using 1
  field_simp [ha, ha2]
  ring

theorem interpolationPowerTest_deriv_hasDerivAt
    {a θ t : ℝ} (ht : 0 < t) (ha : a ≠ 0) (ha2 : a + 2 ≠ 0) :
    HasDerivAt (deriv (interpolationPowerTest a θ))
      ((a + 2 * θ) *
        (interpolationCurvatureKernel t (a + 2 * θ) -
          (1 - θ) * interpolationCurvatureKernel t a -
          θ * interpolationCurvatureKernel t (a + 2))) t := by
  let p := a + 2 * θ
  let g : ℝ → ℝ := fun x =>
    p * x ^ (p - 1) - p * (1 - θ) * x ^ (a - 1) -
      p * θ * x ^ (a + 1)
  have hlocal : deriv (interpolationPowerTest a θ) =ᶠ[𝓝 t] g := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact (interpolationPowerTest_hasDerivAt hx ha ha2).deriv
  have h1 := Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')
  have h3 := Real.hasDerivAt_rpow_const (p := a + 1) (Or.inl ht.ne')
  have hg := ((h1.const_mul p).sub (h2.const_mul (p * (1 - θ)))).sub
    (h3.const_mul (p * θ))
  have hgd : HasDerivAt g
      (p * ((p - 1) * t ^ (p - 2)) -
        p * (1 - θ) * ((a - 1) * t ^ (a - 2)) -
        p * θ * ((a + 1) * t ^ a)) t := by
    convert hg using 1
    simp only [show p - 1 - 1 = p - 2 by ring,
      show a - 1 - 1 = a - 2 by ring,
      show a + 1 - 1 = a by ring]
  convert hgd.congr_of_eventuallyEq hlocal using 1
  dsimp [interpolationCurvatureKernel, p]
  ring

theorem interpolationPowerTest_second_deriv
    {a θ t : ℝ} (ht : 0 < t) (ha : a ≠ 0) (ha2 : a + 2 ≠ 0) :
    deriv (deriv (interpolationPowerTest a θ)) t =
      (a + 2 * θ) *
        (interpolationCurvatureKernel t (a + 2 * θ) -
          (1 - θ) * interpolationCurvatureKernel t a -
          θ * interpolationCurvatureKernel t (a + 2)) :=
  (interpolationPowerTest_deriv_hasDerivAt ht ha ha2).deriv

end SpringerLean

#print axioms SpringerLean.interpolationPowerTest_second_deriv
