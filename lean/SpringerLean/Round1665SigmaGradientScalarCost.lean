import SpringerLean.Round1585EnergySegmentConvex

namespace SpringerLean

/-- Scalar cost of the sigma-cutoff derivative after the two inverse
field projections and the weighted modulus-gradient bound are known. -/
theorem sigma_gradient_scalar_cost_le
    {K t sp u p L dr dy : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hdr : |dr| ≤ 1) (hdy : |dy| ≤ L)
    (hweighted : u*L ≤ 2*u+p/K) :
    (K/2)*sp*u^2*(K*dr+t*dy) ≤
      (K^2/2)*|sp| * u^2+K*t*|sp| * u^2+
        (t*|sp|/2)*u*p := by
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hR : sp*dr ≤ |sp| := by
    calc
      sp*dr ≤ |sp*dr| := le_abs_self _
      _ = |sp| * |dr| := abs_mul _ _
      _ ≤ |sp| * 1 := mul_le_mul_of_nonneg_left hdr (abs_nonneg _)
      _ = |sp| := mul_one _
  have hY : sp*dy ≤ |sp| * L := by
    calc
      sp*dy ≤ |sp*dy| := le_abs_self _
      _ = |sp| * |dy| := abs_mul _ _
      _ ≤ |sp| * L := mul_le_mul_of_nonneg_left hdy (abs_nonneg _)
  have hR' := mul_le_mul_of_nonneg_left hR (le_of_lt hK)
  have hY' := mul_le_mul_of_nonneg_left hY ht
  have hcore : sp*(K*dr+t*dy) ≤ |sp| * (K+t*L) := by
    nlinarith [hR',hY']
  have hfactor : 0 ≤ (K/2)*u^2 := by positivity
  have hmain := mul_le_mul_of_nonneg_left hcore hfactor
  have hw : u^2*L ≤ 2*u^2+u*p/K := by
    have hh := mul_le_mul_of_nonneg_left hweighted hu
    convert hh using 1 <;> ring
  have htfactor : 0 ≤ (K/2)*t*|sp| := by positivity
  have htail := mul_le_mul_of_nonneg_left hw htfactor
  have hidentity : (K/2)*t*|sp| * (2*u^2+u*p/K) =
      K*t*|sp| * u^2+(t*|sp|/2)*u*p := by
    field_simp [hK0]
  calc
    (K/2)*sp*u^2*(K*dr+t*dy) =
      ((K/2)*u^2)*(sp*(K*dr+t*dy)) := by ring
    _ ≤ ((K/2)*u^2)*(|sp| * (K+t*L)) := hmain
    _ = (K^2/2)*|sp| * u^2+(K/2)*t*|sp| * (u^2*L) := by ring
    _ ≤ (K^2/2)*|sp| * u^2+
        (K/2)*t*|sp| * (2*u^2+u*p/K) := by nlinarith [htail]
    _ = _ := by rw [hidentity]; ring

end SpringerLean

#print axioms SpringerLean.sigma_gradient_scalar_cost_le
