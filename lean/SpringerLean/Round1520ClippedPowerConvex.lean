import SpringerLean.Round1519ResidualAntitone
import Mathlib.Analysis.Convex.Piecewise

namespace SpringerLean
set_option maxHeartbeats 320000

def powerTangent (M : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  M^m+(m:ℝ)*M^(m-1)*(x-M)

/-- A convex test which agrees with the positive mth power below M
and follows the supporting tangent above M. -/
noncomputable def clippedTangentPower (M : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  powerTangent M m x +
    (Set.Iic M).piecewise (positivePowerResidual M m) (fun _ => 0) x

theorem clippedTangentPower_convexOn {M : ℝ} (hM : 0 ≤ M)
    {m : ℕ} (hm : 1 ≤ m) :
    ConvexOn ℝ Set.univ (clippedTangentPower M m) := by
  have hp := positivePart_pow_convexOn m hm
  have hres : ConvexOn ℝ (Set.Iic M) (positivePowerResidual M m) := by
    refine ⟨convex_Iic M,?_⟩
    intro x hx y hy a b ha hb hab
    have hpow := hp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at hpow ⊢
    have hlin : powerTangent M m (a*x+b*y) =
        a*powerTangent M m x+b*powerTangent M m y := by
      dsimp [powerTangent]
      rw [show b=1-a by linarith]
      ring
    change (max (a*x+b*y) 0)^m-powerTangent M m (a*x+b*y) ≤
      a*((max x 0)^m-powerTangent M m x)+
      b*((max y 0)^m-powerTangent M m y)
    rw [hlin]
    nlinarith [hpow]
  have hzero : ConvexOn ℝ (Set.Ici M) (fun _ : ℝ => (0:ℝ)) :=
    convexOn_const 0 (convex_Ici M)
  have hzeroMono : MonotoneOn (fun _ : ℝ => (0:ℝ)) (Set.Ici M) :=
    fun _ _ _ _ _ => le_refl _
  have hmatch : positivePowerResidual M m M = 0 := by
    simp [positivePowerResidual,max_eq_left hM]
  have hpiece := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hres hzero (positivePowerResidual_antitone_Iic hM hm) hzeroMono hmatch
  have hlin : ConvexOn ℝ Set.univ (powerTangent M m) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    dsimp [powerTangent]
    rw [show b=1-a by linarith]
    ring_nf
    exact le_rfl
  convert hlin.add hpiece using 1
  rfl

/-- On the actual capped range the convex test is exactly the desired
positive power. -/
theorem clippedTangentPower_eq_positivePart_pow {M x : ℝ}
    (hx : x ≤ M) (m : ℕ) :
    clippedTangentPower M m x = (max x 0)^m := by
  simp [clippedTangentPower,powerTangent,positivePowerResidual,
    Set.piecewise,hx]

/-- Above the cap the clipped test is exactly the affine tangent. -/
theorem clippedTangentPower_eq_tangent {M x : ℝ}
    (hx : M < x) (m : ℕ) :
    clippedTangentPower M m x = powerTangent M m x := by
  simp [clippedTangentPower,Set.piecewise,not_le.mpr hx]

end SpringerLean

#print axioms SpringerLean.clippedTangentPower_convexOn
#print axioms SpringerLean.clippedTangentPower_eq_positivePart_pow
#print axioms SpringerLean.clippedTangentPower_eq_tangent
