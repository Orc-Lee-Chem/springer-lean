import SpringerLean.Round1907PowerTestCurvatureLower
import Mathlib.Analysis.Normed.Module.Convex

namespace SpringerLean

/-- A twice differentiable test on [0,1] with nonnegative curvature and
zero derivative at the origin has a convex even extension to [-1,1]. -/
theorem even_local_convex_of_second_deriv_nonneg
    (f : ℝ → ℝ)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f x)
    (hf'' : DifferentiableOn ℝ (deriv f) (Set.Ioo (0 : ℝ) 1))
    (hzero : deriv f 0 = 0)
    (hcurv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ deriv (deriv f) x) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun x => f |x|) := by
  have hfDiffOn : DifferentiableOn ℝ f (Set.Icc (0 : ℝ) 1) :=
    fun x hx => (hf' x hx).differentiableWithinAt
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f :=
    convexOn_of_deriv2_nonneg (convex_Icc 0 1) hfDiffOn.continuousOn
      (hfDiffOn.mono interior_subset)
      (by simpa only [interior_Icc] using hf'')
      (fun x hx => by
        change 0 ≤ deriv (deriv f) x
        exact hcurv x (by simpa only [interior_Icc] using hx))
  have hderivMono : MonotoneOn (deriv f) (Set.Icc (0 : ℝ) 1) :=
    hconv.monotoneOn_deriv hf'
  have hnonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv f x := by
    intro x hx
    have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := by norm_num
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hh := hderivMono h0 hx' hx.1.le
    simpa only [hzero] using hh
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hfDiffOn.continuousOn
      (hfDiffOn.mono interior_subset) (fun x hx => by
        have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
          simpa only [interior_Icc] using hx
        exact hnonneg x hx')
  have himage : (fun x : ℝ => |x|) '' Set.Icc (-1 : ℝ) 1 =
      Set.Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨abs_nonneg x, abs_le.mpr hx⟩
    · intro hy
      refine ⟨y, ⟨by linarith [hy.1], hy.2⟩, abs_of_nonneg hy.1⟩
  have habs : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun x : ℝ => |x|) := by
    refine ⟨convex_Icc (-1 : ℝ) 1, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have h := abs_add_le (a * x) (b * y)
    simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using h
  rw [← himage] at hconv hmono
  simpa only [Function.comp_def] using hconv.comp habs hmono

end SpringerLean

#print axioms SpringerLean.even_local_convex_of_second_deriv_nonneg
