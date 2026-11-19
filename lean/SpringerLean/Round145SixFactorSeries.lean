import SpringerLean.Round144SixFiniteEnergy

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The formal sixth Faber factor uses the same actual forward coefficients
as the polynomial on the exterior domain. -/
noncomputable def sixthFaberFormalFactor (F : ℂ → ℂ) : PowerSeries ℂ :=
  let φ := formalExteriorPhi (exteriorFormalForward F)
  let b := exteriorForwardCoeff F
  φ ^ 6 -
    PowerSeries.C (6 * b 1) * PowerSeries.X ^ 2 * φ ^ 4 -
    PowerSeries.C (6 * b 2) * PowerSeries.X ^ 3 * φ ^ 3 +
    PowerSeries.C (9 * b 1 ^ 2 - 6 * b 3) *
      PowerSeries.X ^ 4 * φ ^ 2 +
    PowerSeries.C (12 * b 1 * b 2 - 6 * b 4) *
      PowerSeries.X ^ 5 * φ +
    PowerSeries.C (-2 * b 1 ^ 3 + 6 * b 1 * b 3 +
      3 * b 2 ^ 2 - 6 * b 5) * PowerSeries.X ^ 6

/-- Derivative-read Taylor coefficients of the actual sixth Faber factor
agree with the finite formal expression. -/
theorem sixthFaberFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorSeries (sixthFaberFactor F) =
      sixthFaberFormalFactor F := by
  let φ := exteriorPhi F
  let Φ := formalExteriorPhi (exteriorFormalForward F)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  have hφ : AnalyticAt ℂ φ 0 := exteriorPhi_analyticAt F hc.2.2
  have hterm (c : ℂ) (n k : ℕ) :
      actualTaylorSeries (fun u : ℂ => c * u ^ n * φ u ^ k) =
        PowerSeries.C c * PowerSeries.X ^ n * Φ ^ k := by
    have heq : (fun u : ℂ => c * u ^ n * φ u ^ k) =
        (fun u : ℂ => c * (u ^ n * φ u ^ k)) := by
      funext u
      ring
    rw [heq, actualTaylorSeries_const_mul,
      actualTaylorSeries_mul _ _ (by fun_prop : AnalyticAt ℂ (fun u : ℂ => u ^ n) 0)
        (by fun_prop : AnalyticAt ℂ (fun u : ℂ => φ u ^ k) 0),
      actualTaylorSeries_monomial, actualTaylorSeries_pow _ hφ,
      exteriorPhi_actualTaylorSeries F hc]
    simp only [mul_assoc]
    dsimp only [Φ]
  change actualTaylorSeries (fun u : ℂ =>
    φ u ^ 6 - 6 * b₁ * u ^ 2 * φ u ^ 4 -
      6 * b₂ * u ^ 3 * φ u ^ 3 +
      (9 * b₁ ^ 2 - 6 * b₃) * u ^ 4 * φ u ^ 2 +
      (12 * b₁ * b₂ - 6 * b₄) * u ^ 5 * φ u +
      (-2 * b₁ ^ 3 + 6 * b₁ * b₃ +
        3 * b₂ ^ 2 - 6 * b₅) * u ^ 6) = _
  have hm5 : actualTaylorSeries
      (fun u : ℂ => (12 * b₁ * b₂ - 6 * b₄) * u ^ 5 * φ u) =
      PowerSeries.C (12 * b₁ * b₂ - 6 * b₄) *
        PowerSeries.X ^ 5 * Φ := by
    simpa only [pow_one] using hterm (12 * b₁ * b₂ - 6 * b₄) 5 1
  have hm6 : actualTaylorSeries
      (fun u : ℂ => (-2 * b₁ ^ 3 + 6 * b₁ * b₃ +
        3 * b₂ ^ 2 - 6 * b₅) * u ^ 6) =
      PowerSeries.C (-2 * b₁ ^ 3 + 6 * b₁ * b₃ +
        3 * b₂ ^ 2 - 6 * b₅) * PowerSeries.X ^ 6 := by
    simpa only [pow_zero, mul_one] using
      hterm (-2 * b₁ ^ 3 + 6 * b₁ * b₃ +
        3 * b₂ ^ 2 - 6 * b₅) 6 0
  rw [actualTaylorSeries_add _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_add _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_add _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_sub _ _ (by fun_prop) (by fun_prop),
    actualTaylorSeries_pow _ hφ,
    hterm (6 * b₁) 2 4,
    hterm (6 * b₂) 3 3,
    hterm (9 * b₁ ^ 2 - 6 * b₃) 4 2,
    hm5, hm6]
  rw [exteriorPhi_actualTaylorSeries F hc]
  dsimp [sixthFaberFormalFactor, Φ, b₁, b₂, b₃, b₄, b₅]

end SpringerLean
