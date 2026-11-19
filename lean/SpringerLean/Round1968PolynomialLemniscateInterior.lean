import SpringerLean.Round1967SeedExteriorPotential
import Mathlib.FieldTheory.IsAlgClosed.Basic

open Set Polynomial

namespace SpringerLean

/-- Every polynomial zero is an interior point of every positive
sublevel lemniscate of that polynomial. This applies to arbitrary
complex polynomials and supplies the geometric strictness obstruction
for Proposition 9.2. -/
theorem polynomial_zero_mem_interior_lemniscate
    (Q : ℂ[X]) (R : ℝ) (hR : 0 < R)
    (z : ℂ) (hz : Q.eval z = 0) :
    z ∈ interior {w : ℂ | ‖Q.eval w‖ ≤ R} := by
  have hcont : Continuous (fun w : ℂ => ‖Q.eval w‖) := by fun_prop
  have hopen : IsOpen {w : ℂ | ‖Q.eval w‖ < R} :=
    isOpen_lt hcont continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hopen.mem_nhds (by simpa [hz] using hR))
  intro w hw
  exact le_of_lt (show ‖Q.eval w‖ < R from hw)

/-- Every nonconstant complex-polynomial positive lemniscate has
nonempty interior. In particular it cannot itself be a line segment. -/
theorem polynomial_lemniscate_interior_nonempty
    (Q : ℂ[X]) (hQ : 0 < Q.natDegree)
    (R : ℝ) (hR : 0 < R) :
    (interior {w : ℂ | ‖Q.eval w‖ ≤ R}).Nonempty := by
  have hdeg : Q.degree ≠ 0 :=
    (natDegree_pos_iff_degree_pos.mp hQ).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hdeg
  exact ⟨z, polynomial_zero_mem_interior_lemniscate Q R hR z hz⟩

end SpringerLean

#print axioms SpringerLean.polynomial_zero_mem_interior_lemniscate
#print axioms SpringerLean.polynomial_lemniscate_interior_nonempty
