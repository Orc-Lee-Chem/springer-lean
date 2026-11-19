import SpringerLean.FormalReversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open scoped Topology

namespace SpringerLean

/-- Taylor coefficients are read from the actual analytic function. -/
noncomputable def actualTaylorCoeff (h : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n h 0 / (n.factorial : ℂ)

/-- The analytic difference quotient removes the constant term. -/
theorem analyticAt_dslope_zero (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (dslope h 0) 0 :=
  (hh.hasFPowerSeriesAt.has_fpower_series_dslope_fslope).analyticAt

theorem analytic_dslope_decomposition (h : ℂ → ℂ) (u : ℂ) :
    h u = h 0 + u * dslope h 0 u := by
  have hs := sub_smul_dslope h 0 u
  simpa only [sub_zero, smul_eq_mul, add_comm] using (eq_add_of_sub_eq hs.symm)

/-- Removing the constant term shifts every Taylor coefficient by one. -/
theorem actualTaylorCoeff_dslope (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0)
    (n : ℕ) :
    actualTaylorCoeff (dslope h 0) n = actualTaylorCoeff h (n + 1) := by
  have hp := hh.hasFPowerSeriesAt
  have hq := hp.has_fpower_series_dslope_fslope
  have hcanon := (analyticAt_dslope_zero h hh).hasFPowerSeriesAt
  have heq := hcanon.eq_formalMultilinearSeries hq
  have hc := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
  simpa [actualTaylorCoeff, FormalMultilinearSeries.coeff_ofScalars,
    FormalMultilinearSeries.coeff_fslope] using hc

/-- Taylor coefficients only depend on the analytic germ. -/
theorem actualTaylorCoeff_congr {h g : ℂ → ℂ}
    (heq : h =ᶠ[𝓝 (0 : ℂ)] g) (n : ℕ) :
    actualTaylorCoeff h n = actualTaylorCoeff g n := by
  simp only [actualTaylorCoeff]
  rw [Filter.EventuallyEq.iteratedDeriv_eq n heq]

theorem actualTaylorCoeff_forward (F : ℂ → ℂ) (n : ℕ) :
    actualTaylorCoeff (exteriorForwardGerm F) n = exteriorForwardCoeff F n := rfl

theorem actualTaylorCoeff_inverse (F : ℂ → ℂ) (n : ℕ) :
    actualTaylorCoeff (exteriorInverseGerm F) n = exteriorInverseCoeff F n := rfl
/-- Multiplication by the coordinate shifts actual Taylor coefficients. -/
theorem actualTaylorCoeff_var_mul_succ (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    actualTaylorCoeff (fun u : ℂ => u * f u) (k + 1) =
      actualTaylorCoeff f k := by
  have hmul : AnalyticAt ℂ (fun u : ℂ => u * f u) 0 := by
    fun_prop
  have hder : HasDerivAt (fun u : ℂ => u * f u) (f 0) 0 := by
    convert (hasDerivAt_id (0 : ℂ)).mul hf.differentiableAt.hasDerivAt using 1
    · ext u; rfl
    · simp
  have hds : dslope (fun u : ℂ => u * f u) 0 = f := by
    funext u
    by_cases hu : u = 0
    · subst u
      simpa only [dslope_same] using hder.deriv
    · simpa only [sub_zero, smul_eq_mul] using
        (dslope_sub_smul_of_ne (a := (0 : ℂ)) f hu)
  rw [← actualTaylorCoeff_dslope (fun u : ℂ => u * f u) hmul k, hds]

/-- The normalized forward factor has the expected actual Taylor coefficients. -/
theorem actualTaylorCoeff_exteriorPhi_zero (F : ℂ → ℂ) :
    actualTaylorCoeff (exteriorPhi F) 0 = 1 := by
  simp [actualTaylorCoeff, exteriorPhi_zero]

theorem actualTaylorCoeff_exteriorPhi_succ (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    actualTaylorCoeff (exteriorPhi F) (k + 1) =
      exteriorForwardCoeff F k := by
  change actualTaylorCoeff
      (fun u : ℂ => 1 + u * exteriorForwardGerm F u) (k + 1) =
    exteriorForwardCoeff F k
  simp only [actualTaylorCoeff, iteratedDeriv_const_add (by omega : 0 < k + 1)]
  simpa only [actualTaylorCoeff, exteriorForwardCoeff] using
    actualTaylorCoeff_var_mul_succ
      (exteriorForwardGerm F) hc.2.2 k
/-- Power series whose coefficients come from derivatives of the actual function. -/
noncomputable def actualTaylorSeries (h : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (actualTaylorCoeff h)

@[simp] theorem actualTaylorSeries_coeff (h : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (actualTaylorSeries h) = actualTaylorCoeff h n := by
  simp [actualTaylorSeries]

theorem exteriorPhi_actualTaylorSeries (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries (exteriorPhi F) =
      formalExteriorPhi (exteriorFormalForward F) := by
  ext n
  cases n with
  | zero =>
      simp [formalExteriorPhi, actualTaylorCoeff_exteriorPhi_zero]
  | succ k =>
      simpa [formalExteriorPhi, PowerSeries.coeff_succ_X_mul,
        exteriorFormalForward_coeff] using
        (actualTaylorCoeff_exteriorPhi_succ F hc k)
private theorem choose_div_factorial_complex (n i : ℕ) (hi : i ≤ n) :
    (n.choose i : ℂ) / (n.factorial : ℂ) =
      ((i.factorial : ℂ)⁻¹) * (((n - i).factorial : ℂ)⁻¹) := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hi' : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hni : ((n - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  have hfact :
      (n.choose i : ℂ) * (i.factorial : ℂ) *
        ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  field_simp
  exact hfact
/-- Multiplication of analytic functions agrees with multiplication of their
derivative-defined Taylor series. -/
theorem actualTaylorSeries_mul (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    actualTaylorSeries (fun u => f u * g u) =
      actualTaylorSeries f * actualTaylorSeries g := by
  ext n
  rw [PowerSeries.coeff_mul, actualTaylorSeries_coeff]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hprod := iteratedDeriv_mul
    (n := n) (x := (0 : ℂ))
    (hf.contDiffAt.of_le le_top) (hg.contDiffAt.of_le le_top)
  change iteratedDeriv n (f * g) 0 / (n.factorial : ℂ) = _
  rw [hprod]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [actualTaylorSeries_coeff, actualTaylorCoeff]
  calc
    _ = ((n.choose i : ℂ) / (n.factorial : ℂ)) *
          iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 := by ring
    _ = _ := by rw [choose_div_factorial_complex n i hin]; ring
theorem actualTaylorSeries_pow (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) (n : ℕ) :
    actualTaylorSeries (fun u => (h u) ^ n) =
      (actualTaylorSeries h) ^ n := by
  induction n with
  | zero =>
      ext k
      cases k <;> simp [actualTaylorSeries, actualTaylorCoeff,
        iteratedDeriv_const]
  | succ n ih =>
      calc
        actualTaylorSeries (fun u => (h u) ^ (n + 1)) =
            actualTaylorSeries (fun u => (h u) ^ n * h u) := by
              congr 1
        _ = actualTaylorSeries (fun u => (h u) ^ n) *
              actualTaylorSeries h :=
          actualTaylorSeries_mul _ _ (hh.pow n) hh
        _ = (actualTaylorSeries h) ^ (n + 1) := by rw [ih, pow_succ]

theorem exteriorPhi_pow_actualTaylorSeries (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    actualTaylorSeries (fun u => (exteriorPhi F u) ^ n) =
      (formalExteriorPhi (exteriorFormalForward F)) ^ n := by
  rw [actualTaylorSeries_pow _ (exteriorPhi_analyticAt F hc.2.2),
    exteriorPhi_actualTaylorSeries F hc]

/-- The formal residue is the independently derivative-read z⁻¹ coefficient
of the convergent Laurent expansion of the actual function F(z)^n. -/
theorem exteriorFormalResidue_eq_actualLaurentCoeff (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    exteriorFormalResidue F n =
      actualTaylorCoeff (fun u => (exteriorPhi F u) ^ n) (n + 1) := by
  simpa [exteriorFormalResidue] using congrArg
    (PowerSeries.coeff (n + 1))
    (exteriorPhi_pow_actualTaylorSeries F hc n).symm
theorem actualTaylorCoeff_deriv (h : ℂ → ℂ) (k : ℕ) :
    actualTaylorCoeff (deriv h) k =
      (k + 1 : ℂ) * actualTaylorCoeff h (k + 1) := by
  simp only [actualTaylorCoeff]
  have hs : iteratedDeriv (k + 1) h 0 =
      iteratedDeriv k (deriv h) 0 := by
    exact congrFun (iteratedDeriv_succ') 0
  rw [hs, Nat.factorial_succ]
  push_cast
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  field_simp

theorem actualTaylorSeries_deriv (h : ℂ → ℂ) :
    actualTaylorSeries (deriv h) =
      PowerSeries.derivative (actualTaylorSeries h) := by
  ext k
  simpa only [actualTaylorSeries_coeff, PowerSeries.coeff_derivative,
    mul_comm] using actualTaylorCoeff_deriv h k

theorem actualTaylorSeries_dslope_decomposition (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 0) :
    actualTaylorSeries h =
      PowerSeries.C (h 0) +
        PowerSeries.X * actualTaylorSeries (dslope h 0) := by
  ext n
  cases n with
  | zero =>
      simp [actualTaylorSeries, actualTaylorCoeff]
  | succ k =>
      simpa [PowerSeries.coeff_succ_X_mul, actualTaylorSeries_coeff] using
        (actualTaylorCoeff_dslope h hh k).symm
/-- The actual forward power has a convergent Laurent expansion near infinity.
Its z⁻¹ coefficient is the (n+1)-st Taylor coefficient of Φ^n. -/
theorem exteriorF_pow_hasSum_actualLaurent (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    ∀ᶠ u in 𝓝 (0 : ℂ), u ≠ 0 →
      HasSum (fun j : ℕ =>
        actualTaylorCoeff (fun v => (exteriorPhi F v) ^ n) j * u ^ j)
        (u ^ n * (F u⁻¹) ^ n) := by
  have ha : AnalyticAt ℂ (fun v => (exteriorPhi F v) ^ n) 0 :=
    (exteriorPhi_analyticAt F hc.2.2).pow n
  have hs := hasFPowerSeriesAt_iff.mp ha.hasFPowerSeriesAt
  filter_upwards [hs] with u hu hune
  have hsum : HasSum (fun j : ℕ =>
      actualTaylorCoeff (fun v => (exteriorPhi F v) ^ n) j * u ^ j)
      ((exteriorPhi F u) ^ n) := by
    simpa [actualTaylorCoeff, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_comm] using hu
  have heq : u ^ n * (F u⁻¹) ^ n = (exteriorPhi F u) ^ n := by
    rw [exteriorF_pow_reciprocal_phi F hune n]
    calc
      u ^ n * ((u⁻¹) ^ n * (exteriorPhi F u) ^ n) =
          (u * u⁻¹) ^ n * (exteriorPhi F u) ^ n := by ring
      _ = (exteriorPhi F u) ^ n := by simp [hune]
  simpa only [heq] using hsum
end SpringerLean