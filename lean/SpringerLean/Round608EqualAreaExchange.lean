import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

open MeasureTheory Filter
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- Equal-area exchange for a complementary integral. Integrability is
required on both actual complements; the function may be singular inside
their common omitted part. The threshold inequalities are only a.e. -/
theorem equal_area_complement_integral_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (B K : Set X)
    (hB : MeasurableSet B) (hK : MeasurableSet K)
    (hBfin : μ B ≠ ∞) (hKfin : μ K ≠ ∞)
    (harea : μ.real B = μ.real K) (f : X → ℝ) (L : ℝ)
    (hfB : IntegrableOn f Bᶜ μ) (hfK : IntegrableOn f Kᶜ μ)
    (hinside : ∀ᵐ x ∂μ, x ∈ B \ K → L ≤ f x)
    (houtside : ∀ᵐ x ∂μ, x ∈ K \ B → f x ≤ L) :
    (∫ x in Bᶜ, f x ∂μ) ≤ ∫ x in Kᶜ, f x ∂μ := by
  have hrealB := measureReal_inter_add_sdiff (μ := μ) (s := B) hK hBfin
  have hrealK := measureReal_inter_add_sdiff (μ := μ) (s := K) hB hKfin
  rw [Set.inter_comm K B] at hrealK
  have hswap : μ.real (B \ K) = μ.real (K \ B) := by linarith
  have hiA : IntegrableOn f (B \ K) μ := hfK.mono_set (by intro x hx; exact hx.2)
  have hiC : IntegrableOn f (K \ B) μ := hfB.mono_set (by intro x hx; exact hx.2)
  have hiO : IntegrableOn f (Kᶜ ∩ Bᶜ) μ := hfK.mono_set Set.inter_subset_left
  have hcA : IntegrableOn (fun _ : X => L) (B \ K) μ :=
    integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hBfin)
  have hcC : IntegrableOn (fun _ : X => L) (K \ B) μ :=
    integrableOn_const (measure_ne_top_of_subset Set.sdiff_subset hKfin)
  have hlow : L * μ.real (B \ K) ≤ ∫ x in B \ K, f x ∂μ := by
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using
      setIntegral_mono_on_ae hcA hiA (hB.diff hK) hinside
  have hhigh : (∫ x in K \ B, f x ∂μ) ≤ L * μ.real (K \ B) := by
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using
      setIntegral_mono_on_ae hiC hcC (hK.diff hB) houtside
  have hKdecomp : Kᶜ = (B \ K) ∪ (Kᶜ ∩ Bᶜ) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hBdecomp : Bᶜ = (K \ B) ∪ (Kᶜ ∩ Bᶜ) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hdA : Disjoint (B \ K) (Kᶜ ∩ Bᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx ho
    exact ho.2 hx.1
  have hdC : Disjoint (K \ B) (Kᶜ ∩ Bᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hx ho
    exact ho.1 hx.1
  have hki : (∫ x in Kᶜ, f x ∂μ) =
      (∫ x in B \ K, f x ∂μ) + ∫ x in Kᶜ ∩ Bᶜ, f x ∂μ := by
    conv_lhs => rw [hKdecomp]
    exact setIntegral_union hdA (hK.compl.inter hB.compl) hiA hiO
  have hbi : (∫ x in Bᶜ, f x ∂μ) =
      (∫ x in K \ B, f x ∂μ) + ∫ x in Kᶜ ∩ Bᶜ, f x ∂μ := by
    conv_lhs => rw [hBdecomp]
    exact setIntegral_union hdC (hK.compl.inter hB.compl) hiC hiO
  rw [hki,hbi]
  rw [hswap] at hlow
  linarith

end SpringerLean
