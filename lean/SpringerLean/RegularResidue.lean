import SpringerLean.DiskCoeff

namespace SpringerLean

open PowerSeries

/-- The residue is a finite sum of Taylor coefficients of powers of the
same forward correction. This is the algebraic half of the regular filling. -/
theorem formalExteriorPhi_residue_binomial
    (f : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff (n + 1) ((formalExteriorPhi f) ^ n) =
      ∑ p ∈ Finset.range n,
        (n.choose p : ℂ) * PowerSeries.coeff (p + 1) (f ^ (n - p)) := by
  have hterm (p : ℕ) (hp : p ≤ n) :
      PowerSeries.coeff (n + 1)
        ((1 : PowerSeries ℂ) ^ p * (PowerSeries.X * f) ^ (n - p) *
          (n.choose p : PowerSeries ℂ)) =
        (n.choose p : ℂ) * PowerSeries.coeff (p + 1) (f ^ (n - p)) := by
    simp only [one_pow, one_mul, mul_pow]
    rw [mul_comm (PowerSeries.X ^ (n - p)) (f ^ (n - p)),
      PowerSeries.coeff_mul_natCast]
    have hidx : p + 1 + (n - p) = n + 1 := by omega
    rw [← hidx, PowerSeries.coeff_mul_X_pow]
    ring
  have hlast : PowerSeries.coeff (n + 1)
      ((1 : PowerSeries ℂ) ^ n * (PowerSeries.X * f) ^ (n - n) *
        (n.choose n : PowerSeries ℂ)) = 0 := by
    simp [PowerSeries.coeff_one, Nat.succ_ne_zero]
  calc
    PowerSeries.coeff (n + 1) ((formalExteriorPhi f) ^ n) =
        PowerSeries.coeff (n + 1)
          (∑ p ∈ Finset.range (n + 1),
            (1 : PowerSeries ℂ) ^ p * (PowerSeries.X * f) ^ (n - p) *
              (n.choose p : PowerSeries ℂ)) := by
          rw [formalExteriorPhi, add_pow]
    _ = ∑ p ∈ Finset.range (n + 1),
          PowerSeries.coeff (n + 1)
            ((1 : PowerSeries ℂ) ^ p * (PowerSeries.X * f) ^ (n - p) *
              (n.choose p : PowerSeries ℂ)) := by
          rw [map_sum]
    _ = ∑ p ∈ Finset.range n,
          (n.choose p : ℂ) * PowerSeries.coeff (p + 1) (f ^ (n - p)) := by
          rw [Finset.sum_range_succ, hlast, add_zero]
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p (Nat.le_of_lt (Finset.mem_range.mp hp))

/-- The same finite residue sum, with every coefficient read from the actual
regularized forward germ rather than an independent formal input. -/
theorem rescaleExterior_residue_binomial_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    exteriorFormalResidue (rescaleExterior s F) n =
      ∑ p ∈ Finset.range n, (n.choose p : ℂ) *
        actualTaylorCoeff
          (fun u => (exteriorForwardGerm (rescaleExterior s F) u) ^ (n - p))
          (p + 1) := by
  let G := rescaleExterior s F
  have hclass : CenteredExteriorUnivalent G :=
    rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hseries : actualTaylorSeries (exteriorForwardGerm G) =
      exteriorFormalForward G := by
    ext j
    rfl
  rw [exteriorFormalResidue,
    formalExteriorPhi_residue_binomial (exteriorFormalForward G) n]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hpow := actualTaylorSeries_pow
    (exteriorForwardGerm G) hclass.2.2 (n - p)
  rw [hseries] at hpow
  rw [← hpow, actualTaylorSeries_coeff]


end SpringerLean
