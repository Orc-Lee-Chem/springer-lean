import SpringerLean.Round2106PeriodicTopIntegral
import SpringerLean.Round714AngularPairedCandidates

open MeasureTheory Set

namespace SpringerLean

/-- The same paired interval cut works for every continuous periodic
integrand. The geometry and the two translated integrals are reusable
from the earlier angular comparison. -/
theorem periodicTopIntegral_pair_ge_of_gapped_set
    (f : ℝ → ℝ) (hf : Continuous f) {T : ℝ} (hT : 0 < T) (hp : Function.Periodic f T)
    {q p δ ε m : ℝ} (hε0 : 0 ≤ ε) (hεδ : ε < δ)
    (E : Set ℝ) (hEm : MeasurableSet E) (hmass : volume.real E = m)
    (hin : Icc (p-δ) (p+δ) ⊆ E) (hout : E ⊆ Icc (q+δ) (q+T-δ)) :
    (∫ t in E, f (t-ε)) + (∫ t in E, f (t+ε)) ≤
      periodicTopIntegral f T (m+2*ε) + periodicTopIntegral f T (m-2*ε) := by
  let W := verticalShiftWide E ε p
  let N := verticalShiftNarrow E ε p
  let M := verticalShiftMinus E ε
  let P := verticalShiftPlus E ε
  have hb : Bornology.IsBounded E := (Metric.isBounded_Icc _ _).subset hout
  have hMs : M ⊆ Ioc q (q+T) := by
    intro t ht
    have hh := hout ht
    change q+δ ≤ t+ε ∧ t+ε ≤ q+T-δ at hh
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hPs : P ⊆ Ioc q (q+T) := by
    intro t ht
    have hh := hout ht
    change q+δ ≤ t-ε ∧ t-ε ≤ q+T-δ at hh
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hWs : W ⊆ Ioc q (q+T) := by
    intro t ht
    rcases ht with ht | ht
    · exact hMs ht.1
    · exact hPs ht.1
  have hNs : N ⊆ Ioc q (q+T) := by
    intro t ht
    rcases ht with ht | ht
    · exact hPs ht.1
    · exact hMs ht.1
  have hWm : MeasurableSet W := verticalShiftWide_measurable hEm ε p
  have hNm : MeasurableSet N := verticalShiftNarrow_measurable hEm ε p
  have hMm : MeasurableSet M := verticalShiftMinus_measurable hEm ε
  have hPm : MeasurableSet P := verticalShiftPlus_measurable hEm ε
  have hWvol : volume.real W = m+2*ε := by
    rw [← hmass]
    exact verticalShiftWide_measure E hEm hb p δ ε hε0 hεδ hin
  have hNvol : volume.real N = m-2*ε := by
    have h : volume.real N+2*ε = volume.real E :=
      verticalShiftNarrow_measure E hEm hb p δ ε hε0 hεδ hin
    linarith only [h,hmass]
  have hi (S : Set ℝ) (hS : S ⊆ Ioc q (q+T)) : IntegrableOn f S :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set (hS.trans Ioc_subset_Icc_self)
  have hpairs : (∫ t in W, f t)+(∫ t in N, f t) = (∫ t in M, f t)+(∫ t in P, f t) :=
    setIntegral_pair_eq_of_indicator_count f W N M P hWm hNm hMm hPm
      (hi W hWs) (hi N hNs) (hi M hMs) (hi P hPs) (verticalShift_indicator_add E ε p)
  calc
    _ = (∫ t in M, f t)+(∫ t in P, f t) := by
      rw [setIntegral_verticalShiftMinus f E hEm ε,setIntegral_verticalShiftPlus f E hEm ε]
    _ = (∫ t in W, f t)+(∫ t in N, f t) := hpairs.symm
    _ ≤ _ := add_le_add (periodicTopIntegral_candidate_le f hf T _ hT hp q W hWm hWs hWvol)
      (periodicTopIntegral_candidate_le f hf T _ hT hp q N hNm hNs hNvol)

end SpringerLean
