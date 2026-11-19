import SpringerLean.Round1351CircleSinMoment
import SpringerLean.Round1318Catalan359Scalar

namespace SpringerLean

/-- The even sine integral is the same central-binomial scalar that
appears in the inverse Catalan candidate. -/
theorem normalizedCatalanOddMoment_eq_even_sin (m : ℕ) :
    normalizedCatalanOddMoment m =
      (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(2*m+2)) / Real.pi := by
  induction m with
  | zero =>
      simp [normalizedCatalanOddMoment, scaledCatalanMoment,
        integral_sin_sq, Real.sin_zero, Real.sin_pi]
      field_simp [Real.pi_ne_zero]
  | succ m ih =>
      have hrec := integral_sin_pow (a := (0:ℝ))
        (b := Real.pi) (2*m+2)
      have hrec' :
          (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(2*(m+1)+2)) =
          ((2*(m:ℝ)+3)/(2*(m:ℝ)+4)) *
            (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(2*m+2)) := by
        simp [Real.sin_zero, Real.sin_pi, Nat.cast_add,
          Nat.cast_mul] at hrec
        convert hrec using 1 <;> ring_nf
      have hcat := normalizedCatalanOddMoment_step m
      have hden : (0:ℝ) < 2*(m:ℝ)+4 := by positivity
      have hratio : normalizedCatalanOddMoment (m+1) =
          ((2*(m:ℝ)+3)/(2*(m:ℝ)+4)) *
            normalizedCatalanOddMoment m := by
        calc
          _ = ((2*(m:ℝ)+3)*normalizedCatalanOddMoment m)/
              (2*(m:ℝ)+4) := by
            apply (eq_div_iff (ne_of_gt hden)).2
            nlinarith [hcat]
          _ = _ := by ring
      rw [hratio, ih, hrec']
      ring

/-- For an even comparison-circle power, the exact normalized moment
is the Catalan central-binomial scalar. -/
theorem comparisonCircleMoment_even_eq_normalizedCatalan (m : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^(2*m+2)) 0 1 =
      (2:ℝ)^(2*m+2) * normalizedCatalanOddMoment m := by
  rw [comparisonCircleMoment_eq_sinMoment]
  unfold comparisonSinMoment
  rw [normalizedCatalanOddMoment_eq_even_sin]
  ring

/-- Exact identity with the project normalization: if `n=2k-1`, then
`I_(n+1)/2 = n Catalan(k-1)`. -/
theorem comparisonCircleMoment_even_half_eq_scaledCatalan
    (k : ℕ) (hk : 1 ≤ k) :
    Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^(2*k)) 0 1 / 2 =
      (((2*k-1:ℕ):ℝ)) * (catalan (k-1) : ℝ) := by
  have hid : 2*k = 2*(k-1)+2 := by omega
  conv_lhs => rw [hid]
  rw [comparisonCircleMoment_even_eq_normalizedCatalan]
  unfold normalizedCatalanOddMoment
  have hpow : (2:ℝ)^(2*(k-1)+2) = 4*(4:ℝ)^(k-1) := by
    rw [pow_add, show (4:ℝ)=2^2 by norm_num, pow_mul]
    ring
  rw [hpow]
  have hden : (0:ℝ) < 2*(4:ℝ)^(k-1) := by positivity
  have hcast : 2*((k-1:ℕ):ℝ)+1 = ((2*k-1:ℕ):ℝ) := by
    have hnat : 2*(k-1)+1=2*k-1 := by omega
    exact_mod_cast hnat
  calc
    4*(4:ℝ)^(k-1)*
        (scaledCatalanMoment (k-1)/(2*(4:ℝ)^(k-1))) / 2 =
        scaledCatalanMoment (k-1) := by field_simp; ring
    _ = (((2*k-1:ℕ):ℝ))*(catalan (k-1) : ℝ) := by
      rw [scaledCatalanMoment, hcast]

/-- A weak actual Catalan candidate has at least `(1-1/n) I_n`
boundary moment at the comparison-circle normalization. -/
theorem comparisonCircleMoment_candidate_scalar_lower
    (k : ℕ) (hk : 1 ≤ k) :
    (1-1/(((2*k-1:ℕ):ℝ))) *
      Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 ≤
      (((2*k-1:ℕ):ℝ))*(catalan (k-1) : ℝ) := by
  let n : ℕ := 2*k-1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hratio := comparisonCircleMoment_succ_half_ge n hn
  have hid : n+1=2*k := by dsimp [n]; omega
  rw [hid, comparisonCircleMoment_even_half_eq_scaledCatalan k hk] at hratio
  simpa [n] using hratio

end SpringerLean

#print axioms SpringerLean.comparisonCircleMoment_even_half_eq_scaledCatalan
#print axioms SpringerLean.comparisonCircleMoment_candidate_scalar_lower
