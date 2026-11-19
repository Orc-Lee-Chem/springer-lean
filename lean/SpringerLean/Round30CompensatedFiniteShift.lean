import SpringerLean.Round30CompensatedShift
import SpringerLean.Round27CompensatedTruncation

open MeasureTheory Set

namespace SpringerLean

/-- Exact finite-window complement algebra after a vertical translation. The
whole-line term is the integrable difference, never two divergent logarithms. -/
theorem compensated_integral_finite_complements_shift
    (g G : ℝ → ℝ) (S E I : Set ℝ) (ε : ℝ)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hI : MeasurableSet I) (hES : E ⊆ S) (hIS : I ⊆ S)
    (hd : Integrable (fun t => g t - G t))
    (hgS : IntegrableOn (fun t => g (t + ε)) S)
    (hGS : IntegrableOn (fun t => G (t + ε)) S) :
    (∫ t : ℝ, g t - G t) + (∫ t in I, G (t + ε)) -
      (∫ t in E, g (t + ε)) =
    (∫ t in S \ E, g (t + ε)) -
      (∫ t in S \ I, G (t + ε)) +
      (∫ t in Sᶜ, g (t + ε) - G (t + ε)) := by
  have hshift : (∫ t : ℝ, g (t + ε) - G (t + ε)) =
      (∫ t : ℝ, g t - G t) := by
    simpa only using integral_add_right_eq_self (fun t : ℝ => g t - G t) ε
  have h := compensated_integral_finite_complements
    (fun t => g (t + ε)) (fun t => G (t + ε)) S E I
    hS hE hI hES hIS (by simpa only using hd.comp_add_right ε) hgS hGS
  rw [hshift] at h
  exact h

end SpringerLean