import SpringerLean.Round1849ActualRadialTwoSlit

open Filter
open scoped Topology

namespace SpringerLean

theorem actualTaylorCoeff_comp_neg (g : ℂ → ℂ) (n : ℕ) :
    actualTaylorCoeff (fun z => g (-z)) n = (-1 : ℂ) ^ n * actualTaylorCoeff g n := by
  have hh := iteratedDerivWithin_comp_neg (f := g) (n := n) (s := Set.univ) (0 : ℂ)
  have heq : iteratedDeriv n (fun z => g (-z)) 0 =
      (-1 : ℂ) ^ n * iteratedDeriv n g 0 := by
    simpa using hh
  unfold actualTaylorCoeff
  rw [heq]
  ring

theorem actualTaylorCoeff_fun_neg (g : ℂ → ℂ) (n : ℕ) :
    actualTaylorCoeff (fun z => -g z) n = -actualTaylorCoeff g n := by
  have hh := iteratedDerivWithin_fun_neg (f := g) (n := n) (s := Set.univ) (x := (0 : ℂ))
  have heq : iteratedDeriv n (fun z => -g z) 0 = -iteratedDeriv n g 0 := by
    simpa using hh
  unfold actualTaylorCoeff
  rw [heq]
  ring

/-- Exterior oddness is imposed only on the actual exterior domain.
No arbitrary values of F inside the disk enter this coefficient fact. -/
theorem exteriorForwardCoeff_two_eq_zero_of_odd
    (F : ℂ → ℂ)
    (hodd : ∀ z ∈ exteriorDisk, F (-z) = -F z) :
    exteriorForwardCoeff F 2 = 0 := by
  have heq : (fun z : ℂ => exteriorForwardGerm F (-z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => -exteriorForwardGerm F z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    by_cases hz0 : z = 0
    · simp [hz0, exteriorForwardGerm_zero]
    · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      have hi : z⁻¹ ∈ exteriorDisk := by
        change 1 < ‖z⁻¹‖
        rw [norm_inv]
        exact (one_lt_inv₀ hnorm).2 hz1
      rw [exteriorForwardGerm_punctured F (neg_ne_zero.mpr hz0),
        exteriorForwardGerm_punctured F hz0, inv_neg, hodd _ hi]
      ring
  have hh := actualTaylorCoeff_congr heq 2
  rw [actualTaylorCoeff_comp_neg, actualTaylorCoeff_fun_neg] at hh
  norm_num only [even_two, Even.neg_pow, one_pow, one_mul] at hh
  have hmul : (2 : ℂ) * actualTaylorCoeff (exteriorForwardGerm F) 2 = 0 := by
    linear_combination hh
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

end SpringerLean

#print axioms SpringerLean.exteriorForwardCoeff_two_eq_zero_of_odd
