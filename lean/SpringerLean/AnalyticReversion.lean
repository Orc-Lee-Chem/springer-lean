import SpringerLean.TaylorBridge

open scoped Topology

namespace SpringerLean

open PowerSeries

/-- The differential algebra step of analytic coefficient reversion. -/
theorem actual_lagrange_induction_algebra
    (phi h : ℂ → ℂ) (hphi : AnalyticAt ℂ phi 0)
    (hh : AnalyticAt ℂ h 0) (k : ℕ) :
    (k + 1 : ℂ) * actualTaylorCoeff
        (fun u => deriv h u * (phi u) ^ (k + 2)) (k + 1) =
      (k + 2 : ℂ) * actualTaylorCoeff
        (fun u => deriv (fun v => phi v * dslope h 0 v) u *
          (phi u) ^ (k + 1)) k := by
  let q := dslope h 0
  let P := actualTaylorSeries phi
  let Q := actualTaylorSeries q
  have hq : AnalyticAt ℂ q 0 := analyticAt_dslope_zero h hh
  have hpq : AnalyticAt ℂ (fun u => phi u * q u) 0 := hphi.mul hq
  have hprime : actualTaylorSeries (deriv h) =
      Q + PowerSeries.X * PowerSeries.derivative Q := by
    rw [actualTaylorSeries_deriv,
      actualTaylorSeries_dslope_decomposition h hh]
    simp only [map_add, PowerSeries.derivative_C,
      zero_add, PowerSeries.derivative.leibniz]
    simp [PowerSeries.derivative_X, smul_eq_mul]
    ring
  have hleft :
      actualTaylorSeries (fun u => deriv h u * (phi u) ^ (k + 2)) =
        (Q + PowerSeries.X * PowerSeries.derivative Q) * P ^ (k + 2) := by
    have hm := actualTaylorSeries_mul (deriv h)
      (fun u => phi u ^ (k + 2)) hh.deriv (hphi.pow _)
    rw [actualTaylorSeries_pow phi hphi, hprime] at hm
    exact hm
  have hright :
      actualTaylorSeries
          (fun u => deriv (fun v => phi v * q v) u * (phi u) ^ (k + 1)) =
        PowerSeries.derivative (P * Q) * P ^ (k + 1) := by
    have hm := actualTaylorSeries_mul
      (deriv (fun v => phi v * q v)) (fun u => phi u ^ (k + 1))
      hpq.deriv (hphi.pow _)
    rw [actualTaylorSeries_pow phi hphi,
      actualTaylorSeries_deriv,
      actualTaylorSeries_mul phi q hphi hq] at hm
    exact hm
  have hid := formal_reversion_induction_algebra P Q k
  rw [← hleft, ← hright] at hid
  simpa only [actualTaylorSeries_coeff] using hid

private theorem actualTaylorCoeff_zero (h : ℂ → ℂ) :
    actualTaylorCoeff h 0 = h 0 := by
  simp [actualTaylorCoeff]

private theorem actualTaylorCoeff_one (h : ℂ → ℂ) :
    actualTaylorCoeff h 1 = deriv h 0 := by
  simp [actualTaylorCoeff, iteratedDeriv_succ']

/-- Lagrange inversion proved order by order from a local functional equation.
The induction quantifies over all analytic h, so it may be applied to Φq. -/
theorem analytic_lagrange_coefficient (phi V : ℂ → ℂ)
    (hphi : AnalyticAt ℂ phi 0) (hphi0 : phi 0 = 1)
    (hV : AnalyticAt ℂ V 0) (hV0 : V 0 = 0)
    (hVder : deriv V 0 = 1)
    (hfunctional : ∀ᶠ t in 𝓝 (0 : ℂ), V t = t * phi (V t))
    (k : ℕ) :
    ∀ h : ℂ → ℂ, AnalyticAt ℂ h 0 →
      (k + 1 : ℂ) *
        actualTaylorCoeff (fun t => h (V t)) (k + 1) =
      actualTaylorCoeff
        (fun u => deriv h u * (phi u) ^ (k + 1)) k := by
  induction k with
  | zero =>
      intro h hh
      have hhd : HasDerivAt h (deriv h 0) 0 :=
        hh.differentiableAt.hasDerivAt
      have hVD : HasDerivAt V 1 0 := by
        simpa only [hVder] using hV.differentiableAt.hasDerivAt
      have hcomp : deriv (fun t => h (V t)) 0 = deriv h 0 := by
        have hhd' : HasDerivAt h (deriv h 0) (V 0) := by
          simpa only [hV0] using hhd
        have hd := hhd'.comp 0 hVD
        simpa only [hV0, mul_one, Function.comp_def] using hd.deriv
      simp [actualTaylorCoeff_one, actualTaylorCoeff_zero,
        hcomp, hphi0]
  | succ k ih =>
      intro h hh
      let q := dslope h 0
      let m : ℂ → ℂ := fun u => phi u * q u
      have hq : AnalyticAt ℂ q 0 := analyticAt_dslope_zero h hh
      have hm : AnalyticAt ℂ m 0 := hphi.mul hq
      have hmcomp : AnalyticAt ℂ (fun t => m (V t)) 0 := by
        have hm0 : AnalyticAt ℂ m (V 0) := by
          simpa only [hV0] using hm
        exact hm0.comp hV
      have hlocal :
          (fun t => h (V t)) =ᶠ[𝓝 (0 : ℂ)]
            (fun t => h 0 + t * m (V t)) := by
        filter_upwards [hfunctional] with t ht
        change h (V t) = h 0 + t * (phi (V t) * q (V t))
        calc
          h (V t) = h 0 + V t * q (V t) :=
            analytic_dslope_decomposition h (V t)
          _ = h 0 + t * (phi (V t) * q (V t)) := by
            nth_rewrite 1 [ht]
            ring
      have hcoeff :
          actualTaylorCoeff (fun t => h (V t)) (k + 2) =
            actualTaylorCoeff (fun t => m (V t)) (k + 1) := by
        calc
          _ = actualTaylorCoeff (fun t => h 0 + t * m (V t)) (k + 2) :=
            actualTaylorCoeff_congr hlocal (k + 2)
          _ = actualTaylorCoeff (fun t => t * m (V t)) (k + 2) := by
            simp [actualTaylorCoeff,
              iteratedDeriv_const_add (by omega : 0 < k + 2)]
          _ = _ := by
            simpa only [show k + 2 = (k + 1) + 1 by omega] using
              (actualTaylorCoeff_var_mul_succ
                (fun t => m (V t)) hmcomp (k + 1))
      have hIH := ih m hm
      have hAlg := actual_lagrange_induction_algebra phi h hphi hh k
      have hk : (k + 1 : ℂ) ≠ 0 := by
        exact_mod_cast (by omega : k + 1 ≠ 0)
      have hgoal :
          (k + 2 : ℂ) * actualTaylorCoeff
            (fun t => h (V t)) (k + 2) =
          actualTaylorCoeff
            (fun u => deriv h u * phi u ^ (k + 2)) (k + 1) := by
        apply mul_left_cancel₀ hk
        calc
          (k + 1 : ℂ) *
              ((k + 2 : ℂ) * actualTaylorCoeff
                (fun t => h (V t)) (k + 2)) =
            (k + 2 : ℂ) * ((k + 1 : ℂ) *
              actualTaylorCoeff (fun t => m (V t)) (k + 1)) := by
                rw [hcoeff]
                ring
          _ = (k + 2 : ℂ) * actualTaylorCoeff
              (fun u => deriv m u * phi u ^ (k + 1)) k := by
                rw [hIH]
          _ = (k + 1 : ℂ) * actualTaylorCoeff
              (fun u => deriv h u * phi u ^ (k + 2)) (k + 1) := by
                simpa only [m, q] using hAlg.symm
      have hscalar : (((k + 1 : ℕ) : ℂ) + 1) = (k : ℂ) + 2 := by
        push_cast
        ring
      simpa only [show k + 1 + 1 = k + 2 by omega, hscalar] using hgoal

/-- All-order inverse/residue formula for the actual inverse of one paper-class F. -/
theorem exteriorInverseCoeff_succ_mul_eq_formalResidue
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    (k + 1 : ℂ) * exteriorInverseCoeff F (k + 1) =
      exteriorFormalResidue F (k + 1) := by
  let f := exteriorForwardGerm F
  let phi := exteriorPhi F
  obtain ⟨V, hV0, hVa, hVder, hlocal⟩ :=
    exterior_inverse_functional_germs F hc
  have hfunctional : ∀ᶠ t in 𝓝 (0 : ℂ), V t = t * phi (V t) := by
    filter_upwards [hlocal] with t ht
    exact ht.1
  have hinverse :
      (fun t => f (V t)) =ᶠ[𝓝 (0 : ℂ)] exteriorInverseGerm F := by
    filter_upwards [hlocal] with t ht
    exact ht.2.symm
  have hphi : AnalyticAt ℂ phi 0 :=
    exteriorPhi_analyticAt F hc.2.2
  have hlag := analytic_lagrange_coefficient phi V
    hphi (exteriorPhi_zero F) hVa hV0 hVder hfunctional k f hc.2.2
  have hB : actualTaylorCoeff (fun t => f (V t)) (k + 1) =
      exteriorInverseCoeff F (k + 1) := by
    rw [← actualTaylorCoeff_inverse]
    exact actualTaylorCoeff_congr hinverse (k + 1)
  rw [hB] at hlag
  have hfseries : actualTaylorSeries f = exteriorFormalForward F := by
    ext n
    rfl
  have hseries :
      actualTaylorSeries
          (fun u => deriv f u * phi u ^ (k + 1)) =
        PowerSeries.derivative (exteriorFormalForward F) *
          (formalExteriorPhi (exteriorFormalForward F)) ^ (k + 1) := by
    have hm := actualTaylorSeries_mul (deriv f)
      (fun u => phi u ^ (k + 1)) hc.2.2.deriv (hphi.pow _)
    rw [actualTaylorSeries_deriv,
      actualTaylorSeries_pow phi hphi,
      hfseries, exteriorPhi_actualTaylorSeries F hc] at hm
    exact hm
  have hcoeff := congrArg (PowerSeries.coeff k) hseries
  simp only [actualTaylorSeries_coeff] at hcoeff
  rw [hcoeff, formalExteriorPhi_residue_identity] at hlag
  simpa [exteriorFormalResidue, show k + 1 + 1 = k + 2 by omega] using hlag

/-- The paper's nB_n=[z⁻¹]F(z)^n for each positive integer n. -/
theorem exteriorInverseCoeff_mul_eq_formalResidue
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) * exteriorInverseCoeff F n = exteriorFormalResidue F n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa [Nat.succ_eq_add_one, Nat.cast_add] using
    exteriorInverseCoeff_succ_mul_eq_formalResidue F hc k
end SpringerLean