import SpringerLean.Round1353CirclePlatformLower
import SpringerLean.Round1337PlatformScalar
import SpringerLean.Round658ActualBoundaryMoment

namespace SpringerLean

/-- The two-sided localization platform is now paid by the *actual*
comparison-circle moment, with no abstract moment premise. -/
theorem comparisonCircle_platform_bound
    (k : ℕ) (hk : 751 ≤ k) :
    2*(39/20 : ℝ)^(2*k-1) ≤
      Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 /
        (((2*k-1:ℕ):ℝ)) := by
  let n : ℕ := 2*k-1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hI := comparisonCircleMoment_odd_platform_lower k hk
  exact platform_le_of_moment_lower n hn hI

/-- A weak actual Catalan candidate forces the claimed normalized
moment lower bound on every smooth exterior dilate. No a.e. radial
trace or boundary Parseval theorem is assumed. -/
theorem actual_candidate_regularBoundary_moment_ge_circle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤
      ‖exteriorInverseCoeff F (2*k-1)‖)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    s^(2*k) * (1-1/(((2*k-1:ℕ):ℝ))) *
      Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 ≤
      Real.circleAverage
        (fun ζ : ℂ => ‖rescaleExterior s F ζ‖^(2*k-1)) 0 1 := by
  let n : ℕ := 2*k-1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hscalar := comparisonCircleMoment_candidate_scalar_lower k (by omega)
  have hactual := rescaleExterior_boundary_moment_ge_of_inverseCoeff_candidate
    F hc hs0 hs1 n hn (catalan (k-1) : ℝ) hB
  have hspow : 0 ≤ s^(n+1) := pow_nonneg hs0.le _
  have hmult := mul_le_mul_of_nonneg_left hscalar hspow
  have hnk : n+1=2*k := by dsimp [n]; omega
  rw [show s^(2*k)=s^(n+1) by rw [hnk]]
  change s^(n+1) * (1-1/(n:ℝ)) *
    Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 ≤ _
  calc
    _ = s^(n+1) * ((1-1/(n:ℝ)) *
        Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1) := by ring
    _ ≤ s^(n+1) * ((n:ℝ)*(catalan (k-1) : ℝ)) := by
      simpa [n] using hmult
    _ ≤ Real.circleAverage
        (fun ζ : ℂ => ‖rescaleExterior s F ζ‖^n) 0 1 := by
      simpa only [mul_assoc] using hactual

end SpringerLean

#print axioms SpringerLean.comparisonCircle_platform_bound
#print axioms SpringerLean.actual_candidate_regularBoundary_moment_ge_circle
