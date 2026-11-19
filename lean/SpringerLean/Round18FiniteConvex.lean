import SpringerLean.Round18SignReduction

open MeasureTheory Metric

namespace SpringerLean

/-- A finite affine-plus-hinge convex test. Nonnegative hinge weights
encode convexity of this piecewise linear test. -/
noncomputable def finiteHingeTest {ι : Type*} (S : Finset ι)
    (w t : ι → ℝ) (p q x : ℝ) : ℝ :=
  p + q * x + ∑ i ∈ S, w i * max (x - t i) 0

/-- Equal means and all selected positive-part comparisons imply the
comparison for every finite convex hinge test. -/
theorem circleAverage_finiteHingeTest_le
    {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (X Y : ℂ → ℝ)
    (hX : ContinuousOn X (sphere (0 : ℂ) 1))
    (hY : ContinuousOn Y (sphere (0 : ℂ) 1))
    (hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hhinge : ∀ i ∈ S,
      Real.circleAverage (fun ζ => max (X ζ - t i) 0) 0 1 ≤
      Real.circleAverage (fun ζ => max (Y ζ - t i) 0) 0 1)
    (p q : ℝ) :
    Real.circleAverage (fun ζ => finiteHingeTest S w t p q (X ζ)) 0 1 ≤
      Real.circleAverage (fun ζ => finiteHingeTest S w t p q (Y ζ)) 0 1 := by
  have havg (Z : ℂ → ℝ) (hZ : ContinuousOn Z (sphere (0 : ℂ) 1)) :
      Real.circleAverage (fun ζ => finiteHingeTest S w t p q (Z ζ)) 0 1 =
        p + q * Real.circleAverage Z 0 1 +
          ∑ i ∈ S, w i *
            Real.circleAverage (fun ζ => max (Z ζ - t i) 0) 0 1 := by
    have hZi : CircleIntegrable Z 0 1 := hZ.circleIntegrable (by norm_num)
    have hHi (i : ι) : CircleIntegrable
        (fun ζ => max (Z ζ - t i) 0) 0 1 := by
      have hc : ContinuousOn (fun ζ => max (Z ζ - t i) 0)
          (sphere (0 : ℂ) 1) := by fun_prop
      exact hc.circleIntegrable (by norm_num)
    have hWi (i : ι) : CircleIntegrable
        (fun ζ => w i * max (Z ζ - t i) 0) 0 1 := by
      have hc : ContinuousOn (fun ζ => w i * max (Z ζ - t i) 0)
          (sphere (0 : ℂ) 1) := by fun_prop
      exact hc.circleIntegrable (by norm_num)
    have hq : CircleIntegrable (fun ζ => q * Z ζ) 0 1 :=
      (continuousOn_const.mul hZ).circleIntegrable (by norm_num)
    have hsum : CircleIntegrable
        (fun ζ => ∑ i ∈ S, w i * max (Z ζ - t i) 0) 0 1 := by
      have h : CircleIntegrable
          (∑ i ∈ S, fun ζ => w i * max (Z ζ - t i) 0) 0 1 :=
        CircleIntegrable.sum S (fun i _ => hWi i)
      convert h using 1
      funext ζ
      simp only [Finset.sum_apply]
    have hbase : CircleIntegrable (fun ζ => p + q * Z ζ) 0 1 :=
      (circleIntegrable_const _ _ _).add hq
    calc
      Real.circleAverage (fun ζ => finiteHingeTest S w t p q (Z ζ)) 0 1 =
          Real.circleAverage (fun ζ => (p + q * Z ζ) +
            ∑ i ∈ S, w i * max (Z ζ - t i) 0) 0 1 := rfl
      _ = Real.circleAverage (fun ζ => p + q * Z ζ) 0 1 +
          Real.circleAverage (fun ζ => ∑ i ∈ S, w i * max (Z ζ - t i) 0) 0 1 :=
        Real.circleAverage_fun_add hbase hsum
      _ = p + q * Real.circleAverage Z 0 1 +
          ∑ i ∈ S, w i *
            Real.circleAverage (fun ζ => max (Z ζ - t i) 0) 0 1 := by
        rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hq,
          Real.circleAverage_const,
          show Real.circleAverage (fun ζ => q * Z ζ) 0 1 =
            q * Real.circleAverage Z 0 1 from
              (by simpa only [smul_eq_mul] using
                (Real.circleAverage_fun_smul (a := q) (f := Z) (c := 0) (R := 1)))]
        rw [Real.circleAverage_fun_sum]
        · simp_rw [show ∀ i : ι,
            Real.circleAverage (fun ζ => w i * max (Z ζ - t i) 0) 0 1 =
              w i * Real.circleAverage (fun ζ => max (Z ζ - t i) 0) 0 1 from
                fun i => by simpa only [smul_eq_mul] using
                  (Real.circleAverage_fun_smul (a := w i)
                    (f := fun ζ => max (Z ζ - t i) 0) (c := 0) (R := 1))]
        · intro i hi
          exact hWi i
  rw [havg X hX, havg Y hY, hmean]
  simp only [add_le_add_iff_left]
  exact Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (hhinge i hi) (hw i hi))

end SpringerLean
