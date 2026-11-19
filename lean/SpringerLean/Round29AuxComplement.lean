import SpringerLean.Round29AuxErrorBound
import SpringerLean.Round29ReferenceKernel
import SpringerLean.Round25Optimizer

open MeasureTheory Set

namespace SpringerLean

/-- A compensated whole-line comparison is bounded by the complement L¹ errors
when the reference kernel is minimized by the comparison set. -/
theorem compensated_auxiliary_le_reference_complement_errors
    (g G k : ℝ → ℝ) (E I : Set ℝ)
    (hE : MeasurableSet E) (hI : MeasurableSet I)
    (heg : Integrable (fun t => g t - k t))
    (heG : Integrable (fun t => G t - k t))
    (hkE : IntegrableOn k E) (hkI : IntegrableOn k I)
    (hkmin : (∫ t in I, k t) ≤ ∫ t in E, k t) :
    (∫ t : ℝ, g t - G t) + (∫ t in I, G t) - (∫ t in E, g t) ≤
      (∫ t in Eᶜ, |g t - k t|) + (∫ t in Iᶜ, |G t - k t|) := by
  let eg : ℝ → ℝ := fun t => g t - k t
  let eG : ℝ → ℝ := fun t => G t - k t
  have hd : Integrable (fun t => g t - G t) := by
    convert heg.sub heG using 1
    funext t
    dsimp [eg, eG]
    ring
  have hgE : IntegrableOn g E := by
    have h := heg.integrableOn.add hkE
    convert h using 1
    funext t
    dsimp [eg]
    ring
  have hGE : IntegrableOn G I := by
    have h := heG.integrableOn.add hkI
    convert h using 1
    funext t
    dsimp [eG]
    ring
  have hsplitg := integral_add_compl hE heg
  have hsplitG := integral_add_compl hI heG
  have hsub : (∫ t : ℝ, g t - G t) = (∫ t : ℝ, eg t) - ∫ t : ℝ, eG t := by
    have hfun : (fun t => g t - G t) = (fun t => eg t - eG t) := by
      funext t
      dsimp [eg, eG]
      ring
    rw [hfun, integral_sub heg heG]
  have hGE' : (∫ t in I, G t) = (∫ t in I, eG t) + ∫ t in I, k t := by
    have hfun : G = fun t => eG t + k t := by
      funext t
      dsimp [eG]
      ring
    rw [hfun, integral_add heG.integrableOn hkI]
  have hgE' : (∫ t in E, g t) = (∫ t in E, eg t) + ∫ t in E, k t := by
    have hfun : g = fun t => eg t + k t := by
      funext t
      dsimp [eg]
      ring
    rw [hfun, integral_add heg.integrableOn hkE]
  have hupperg : (∫ t in Eᶜ, eg t) ≤ ∫ t in Eᶜ, |eg t| :=
    integral_mono heg.integrableOn heg.abs.integrableOn (fun t => le_abs_self _)
  have hupperG : -(∫ t in Iᶜ, eG t) ≤ ∫ t in Iᶜ, |eG t| := by
    rw [← integral_neg]
    exact integral_mono heG.neg.integrableOn heG.abs.integrableOn
      (fun t => neg_le_abs _)
  rw [hsub, hGE', hgE', ← hsplitg, ← hsplitG]
  linarith

end SpringerLean
