import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SpringerLean

/-- The open exterior unit disk used in the manuscript. -/
def exteriorDisk : Set ℂ := {z | 1 < ‖z‖}

/-- The centered rotated slit map `J_a(z) = z + a/z`. -/
noncomputable def slitMap (a z : ℂ) : ℂ := z + a / z

theorem exterior_ne_zero {z : ℂ} (hz : z ∈ exteriorDisk) : z ≠ 0 := by
  intro h
  simp [exteriorDisk, h] at hz
  linarith

theorem id_injOn_exterior : Set.InjOn (fun z : ℂ => z) exteriorDisk := by
  intro z _ w _ h
  exact h

/-- The actual slit map is injective on the whole open exterior disk. -/
theorem slitMap_injOn (a : ℂ) (ha : ‖a‖ = 1) :
    Set.InjOn (slitMap a) exteriorDisk := by
  intro z hz w hw h
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  have hw0 : w ≠ 0 := exterior_ne_zero hw
  have hp : (z - w) * (z * w - a) = 0 := by
    calc
      (z - w) * (z * w - a) = (slitMap a z - slitMap a w) * (z * w) := by
        dsimp [slitMap]
        field_simp [hz0, hw0]
        ring
      _ = 0 := by rw [h]; ring
  rcases mul_eq_zero.mp hp with hzw | hzw
  · exact sub_eq_zero.mp hzw
  · have hn : ‖z * w‖ = 1 := by rw [sub_eq_zero.mp hzw, ha]
    have hz1 : 1 < ‖z‖ := hz
    have hw1 : 1 < ‖w‖ := hw
    rw [norm_mul] at hn
    nlinarith [mul_pos (sub_pos.mpr hz1) (sub_pos.mpr hw1)]


/-- Every point of the actual image has exactly one exterior preimage. -/
theorem slitMap_unique_preimage (a : ℂ) (ha : ‖a‖ = 1) (w : ℂ)
    (hw : w ∈ slitMap a '' exteriorDisk) :
    ∃! z : ℂ, z ∈ exteriorDisk ∧ slitMap a z = w := by
  rcases hw with ⟨z, hz, rfl⟩
  refine ⟨z, ⟨hz, rfl⟩, ?_⟩
  intro y hy
  exact (slitMap_injOn a ha) hy.1 hz hy.2

/-- The equation satisfied by the actual inverse branch, wherever it is defined. -/
theorem slitMap_eq_iff_quadratic (a z w : ℂ) (hz : z ≠ 0) :
    slitMap a z = w ↔ z * z - w * z + a = 0 := by
  have hfactor : z * z - w * z + a = (slitMap a z - w) * z := by
    dsimp [slitMap]
    field_simp [hz]
    ring
  constructor
  · intro h
    rw [hfactor, h]
    ring
  · intro h
    rw [hfactor] at h
    rcases mul_eq_zero.mp h with h | h
    · exact sub_eq_zero.mp h
    · exact (hz h).elim

/-- At the boundary, the classical slit map identifies two distinct points. -/
theorem slitMap_one_boundary_collision :
    Complex.I ≠ -Complex.I ∧
      ‖(Complex.I : ℂ)‖ = 1 ∧ ‖(-Complex.I : ℂ)‖ = 1 ∧
      slitMap 1 Complex.I = slitMap 1 (-Complex.I) := by
  constructor
  · intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  constructor
  · simp
  constructor
  · simp
  · simp [slitMap, div_eq_mul_inv]
end SpringerLean
