import SpringerLean.Round1910ProjectionFirstModeCircle
import SpringerLean.Round11Energy

open scoped ComplexConjugate

namespace SpringerLean

/-- Choose the projection direction so that the leading exterior mode and
the reflected first Laurent mode have the same phase. -/
theorem projection_first_mode_phase_max (B : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ‖conj c + c * B‖ = 1 + ‖B‖ := by
  obtain ⟨c, hc, hphase⟩ := exists_unit_phase_align B
  refine ⟨c, hc, ?_⟩
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj']
    norm_cast
    simp [hc]
  have hreal : (c * (conj c + c * B)).re = 1 + ‖B‖ := by
    rw [mul_add, hcc]
    have hh : c * (c * B) = c ^ 2 * B := by ring
    rw [hh, Complex.add_re, Complex.one_re, hphase]
  have hmulnorm : ‖c * (conj c + c * B)‖ = ‖conj c + c * B‖ := by
    rw [norm_mul, hc, one_mul]
  have hlow : 1 + ‖B‖ ≤ ‖conj c + c * B‖ := by
    rw [← hreal, ← hmulnorm]
    exact le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hupp : ‖conj c + c * B‖ ≤ 1 + ‖B‖ := by
    calc
      _ ≤ ‖conj c‖ + ‖c * B‖ := norm_add_le _ _
      _ = 1 + ‖B‖ := by rw [Complex.norm_conj, norm_mul, hc, one_mul]
  exact le_antisymm hupp hlow

/-- A smooth-circle version of the first-mode projection estimate for the
actual exterior map. The radial limit is handled in the next bridge. -/
theorem projectionAnalytic_circle_energy_phase_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (1 + ‖exteriorForwardCoeff F 1‖) ^ 2 * r ^ 2 ≤
        Real.circleAverage
          (fun z : ℂ => ‖projectionAnalytic F c z‖ ^ 2) 0 r := by
  obtain ⟨c, hcnorm, heq⟩ :=
    projection_first_mode_phase_max (exteriorForwardCoeff F 1)
  refine ⟨c, hcnorm, ?_⟩
  rw [← heq]
  exact projectionAnalytic_circle_energy_first_mode F hc c hr0 hr1

end SpringerLean

#print axioms SpringerLean.projectionAnalytic_circle_energy_phase_bound
