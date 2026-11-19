import SpringerLean.Round248LinearFormalLog

namespace SpringerLean
open PowerSeries

/-- After a coefficient-ring map making the inner variable invertible,
the difference quotient factors into two series normalized at one. -/
theorem formalFaberKernel_mapped_factorization
    {A B : Type*} [CommRing A] [Field B]
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 0)
    (h : PowerSeries A →+* B) (hy : h PowerSeries.X ≠ 0) :
    let φ := 1 + PowerSeries.X * f
    let T := PowerSeries.map h (formalFaberKernel f)
    let ψ := PowerSeries.map (h.comp PowerSeries.C) φ
    let p := (h PowerSeries.X)⁻¹
    let w := p * h φ
    (1 - PowerSeries.C p * PowerSeries.X) * (1 - T) =
      ψ - PowerSeries.C w * PowerSeries.X := by
  dsimp only
  let φ := 1 + PowerSeries.X * f
  let T := PowerSeries.map h (formalFaberKernel f)
  let ψ := PowerSeries.map (h.comp PowerSeries.C) φ
  let p := (h PowerSeries.X)⁻¹
  have hm := congrArg (PowerSeries.map h)
    (formalFaberKernel_factorization f hf)
  change PowerSeries.map h
      ((PowerSeries.C (PowerSeries.X : PowerSeries A) - PowerSeries.X) *
        (1 - formalFaberKernel f)) =
    PowerSeries.map h
      (PowerSeries.C (PowerSeries.X : PowerSeries A) *
          PowerSeries.map PowerSeries.C φ - PowerSeries.X * PowerSeries.C φ) at hm
  simp only [map_mul, map_sub, map_one,
    PowerSeries.map_C, PowerSeries.map_X] at hm
  have hcomp : PowerSeries.map h (PowerSeries.map PowerSeries.C φ) = ψ := by
    rfl
  rw [hcomp] at hm
  change (PowerSeries.C (h PowerSeries.X) - PowerSeries.X) * (1 - T) =
    PowerSeries.C (h PowerSeries.X) * ψ - PowerSeries.X * PowerSeries.C (h φ) at hm
  have hp : (PowerSeries.C p : PowerSeries B) *
      PowerSeries.C (h PowerSeries.X) = 1 := by
    rw [← map_mul]
    simp [p, hy]
  change (1 - PowerSeries.C p * PowerSeries.X) * (1 - T) =
    ψ - PowerSeries.C (p * h φ) * PowerSeries.X
  calc
    _ = PowerSeries.C p *
        ((PowerSeries.C (h PowerSeries.X) - PowerSeries.X) * (1 - T)) := by
      calc
        _ = ((PowerSeries.C p * PowerSeries.C (h PowerSeries.X)) -
          PowerSeries.C p * PowerSeries.X) * (1 - T) := by rw [hp]
        _ = _ := by ring
    _ = PowerSeries.C p *
        (PowerSeries.C (h PowerSeries.X) * ψ -
          PowerSeries.X * PowerSeries.C (h φ)) := by rw [hm]
    _ = _ := by
      rw [map_mul]
      calc
        _ = (PowerSeries.C p * PowerSeries.C (h PowerSeries.X)) * ψ -
          (PowerSeries.C p * PowerSeries.C (h φ)) * PowerSeries.X := by ring
        _ = _ := by rw [hp]; ring

/-- Uniform logarithmic Faber factorization. This is an algebraic identity
for every order, before extraction of the Faber polynomial coefficient. -/
theorem formalFaberKernel_mapped_log_identity
    {A B : Type*} [CommRing A] [Field B]
    [Algebra ℚ B]
    (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 0)
    (h : PowerSeries A →+* B) (hy : h PowerSeries.X ≠ 0) :
    let φ := 1 + PowerSeries.X * f
    let T := PowerSeries.map h (formalFaberKernel f)
    let ψ := PowerSeries.map (h.comp PowerSeries.C) φ
    let p := (h PowerSeries.X)⁻¹
    let w := p * h φ;
    (-PowerSeries.logOf (ψ - PowerSeries.C w * PowerSeries.X)) =
      (-PowerSeries.logOf (1 - PowerSeries.C p * PowerSeries.X)) +
        (-PowerSeries.logOf (1 - T)) := by
  dsimp only
  have hfactor := formalFaberKernel_mapped_factorization f hf h hy
  dsimp only at hfactor
  rw [← hfactor]
  rw [formal_logOf_mul]
  · abel
  · simp
  · simp [← PowerSeries.coeff_zero_eq_constantCoeff,
      formalFaberKernel]

end SpringerLean
