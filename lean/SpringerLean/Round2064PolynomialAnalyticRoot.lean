import SpringerLean.Round2063ReciprocalRootCoordinate
import Mathlib.Analysis.Calculus.Deriv.Mul

open Polynomial Set Metric Filter
open scoped Topology

namespace SpringerLean

private theorem reciprocal_factor_hasDerivAt_zero (s : Multiset ℂ) (b : ℂ) :
    HasDerivAt (fun u : ℂ => (s.map (fun a => 1 - (a-b)*u)).prod)
      ((s.map (fun a => b-a)).sum) 0 := by
  induction s using Multiset.induction_on with
  | empty => simpa using (hasDerivAt_const (0 : ℂ) (1 : ℂ))
  | cons a s ih =>
    have hlin : HasDerivAt (fun u : ℂ => 1-(a-b)*u) (b-a) 0 := by
      have heq : 0 - (a-b) * 1 = b-a := by ring
      simpa only [Pi.sub_def, id_eq, heq] using
        ((hasDerivAt_const (0:ℂ) (1:ℂ)).sub
          ((hasDerivAt_id (0:ℂ)).const_mul (a-b)))
    have hprod : (s.map (fun _ : ℂ => (1 : ℂ))).prod = 1 := by simp
    simpa only [Pi.mul_def, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
      mul_zero, sub_zero, hprod, mul_one, one_mul] using hlin.mul ih

/-- Construct the analytic (n)th-root coordinate of a monic polynomial
on the entire complement of its connected unit lemniscate. The
reciprocal normalization records the derivative needed for centering. -/
theorem connectedPolynomial_analytic_root_coordinate
    (Q : ℂ[X]) (hQ : Q.Monic) (hn : 0 < Q.natDegree)
    (hsum : Q.roots.sum = 0)
    (hconn : IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1}) :
    ∃ b : ℂ, ‖Q.eval b‖ ≤ 1 ∧ ∃ H : ℂ → ℂ,
      let B := fun z : ℂ => (z-b)*H ((z-b)⁻¹)
      H 0 = 1 ∧ AnalyticAt ℂ H 0 ∧ HasDerivAt H b 0 ∧
      AnalyticOnNhd ℂ B {z : ℂ | 1 < ‖Q.eval z‖} ∧
      ∀ z : ℂ, 1 < ‖Q.eval z‖ → (B z)^Q.natDegree = Q.eval z := by
  classical
  obtain ⟨b, hb⟩ := hconn.nonempty
  let K := (fun z : ℂ => z-b) '' {z : ℂ | ‖Q.eval z‖ ≤ 1}
  obtain ⟨hK, hKconn, hK0, hU⟩ :=
    translated_lemniscate_reciprocal_properties Q hn hconn b hb
  let U := reciprocalSeparation K 0
  have hUO : IsOpen U := reciprocalSeparation_isOpen K hK 0
  have hU0 : (0 : ℂ) ∈ U := zero_mem_reciprocalSeparation K 0
  have hlog (a : ℂ) (ha : a ∈ Q.roots) :
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L U ∧ L 0 = 0 ∧
        ∀ u ∈ U, Complex.exp (L u) = 1-(a-b)*u := by
    have hmem : a-b ∈ K := by
      have ha0 : Q.eval a = 0 := (mem_roots hQ.ne_zero).mp ha
      exact ⟨a, by change ‖Q.eval a‖ ≤ 1; rw [ha0, norm_zero]; norm_num, rfl⟩
    obtain ⟨L,hL,hL0,hE⟩ := reciprocal_ratio_global_analytic_log K hK hKconn hU
      (a-b) 0 hmem hK0
    exact ⟨L,hL,hL0,fun u hu => by simpa using hE u hu⟩
  let L : ℂ → (ℂ → ℂ) := fun a =>
    if ha : a ∈ Q.roots then (hlog a ha).choose else 0
  have hL (a : ℂ) (ha : a ∈ Q.roots) :
      AnalyticOnNhd ℂ (L a) U ∧ L a 0 = 0 ∧
        ∀ u ∈ U, Complex.exp (L a u) = 1-(a-b)*u := by
    simpa only [L, dite_eq_left ha] using (hlog a ha).choose_spec
  have hmultiset : ∀ s : Multiset ℂ, (∀ a ∈ s, a ∈ Q.roots) →
      AnalyticOnNhd ℂ (fun u => (s.map (fun a => L a u)).sum) U ∧
      (s.map (fun a => L a 0)).sum = 0 ∧
      ∀ u ∈ U, Complex.exp ((s.map (fun a => L a u)).sum) =
        (s.map (fun a => 1-(a-b)*u)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp [analyticOnNhd_const]
    | cons a s ih =>
      intro hs
      have ha := hL a (hs a (Multiset.mem_cons_self _ _))
      have hr := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
      exact ⟨ha.1.add hr.1, by simp [ha.2.1, hr.2.1],
        fun u hu => by rw [Complex.exp_add, ha.2.2 u hu, hr.2.2 u hu]⟩
  obtain ⟨hS,hS0,hSexp⟩ := hmultiset Q.roots (fun _ h => h)
  let H : ℂ → ℂ := fun u =>
    Complex.exp (((Q.roots.map (fun a => L a u)).sum) / (Q.natDegree : ℂ))
  have hn0 : (Q.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hH : AnalyticOnNhd ℂ H U := by
    intro u hu
    exact (hS u hu).div_const.cexp
  have hH0 : H 0 = 1 := by simp [H,hS0]
  have hpow (u : ℂ) (hu : u ∈ U) : H u ^ Q.natDegree =
      (Q.roots.map (fun a => 1-(a-b)*u)).prod := by
    dsimp only [H]
    rw [← Complex.exp_nat_mul]
    rw [mul_comm, div_mul_cancel₀ _ hn0, hSexp u hu]
  have hsum' : (Q.roots.map (fun a => b-a)).sum = (Q.natDegree : ℂ)*b := by
    have hcard := (IsAlgClosed.splits Q).natDegree_eq_card_roots
    rw [hcard]
    have aux (s : Multiset ℂ) :
        (s.map (fun a => b-a)).sum = (s.card : ℂ)*b - s.sum := by
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [ih, Nat.cast_succ]; ring
    rw [aux, hsum, sub_zero]
  have hD : HasDerivAt H b 0 := by
    have he := (((hH 0 hU0).differentiableAt.hasDerivAt).pow Q.natDegree)
    have hprod := (reciprocal_factor_hasDerivAt_zero Q.roots b)
    rw [hsum'] at hprod
    have he' := he.congr_of_eventuallyEq (by
      filter_upwards [hUO.mem_nhds hU0] with u hu
      exact (hpow u hu).symm)
    have hid := he'.unique hprod
    rw [hH0, one_pow, mul_one] at hid
    have hDb := mul_left_cancel₀ hn0 hid
    simpa only [hDb] using (hH 0 hU0).differentiableAt.hasDerivAt
  let B := fun z : ℂ => (z-b)*H ((z-b)⁻¹)
  have hUmem (z : ℂ) (hz : 1 < ‖Q.eval z‖) : (z-b)⁻¹ ∈ U := by
    have hzb : z-b ≠ 0 := by
      intro h
      rw [sub_eq_zero.mp h] at hz
      exact (not_lt_of_ge hb) hz
    apply (mem_reciprocalSeparation_zero_iff K (inv_ne_zero hzb)).mpr
    intro h
    rw [inv_inv] at h
    obtain ⟨w, hw, hwz⟩ := h
    have heq : w = z := by linear_combination hwz
    subst w
    exact (not_lt_of_ge hw) hz
  refine ⟨b,hb,H,hH0,hH 0 hU0,hD,?_,?_⟩
  · intro z hz
    change 1 < ‖Q.eval z‖ at hz
    have hzb : z-b ≠ 0 := by
      intro h
      exact (not_lt_of_ge hb) (sub_eq_zero.mp h ▸ hz)
    have hi : AnalyticAt ℂ (fun u : ℂ => (u-b)⁻¹) z :=
      (by fun_prop : AnalyticAt ℂ (fun u : ℂ => u-b) z).inv hzb
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z-b) z).mul
      (AnalyticAt.comp (f := fun u : ℂ => (u-b)⁻¹) (hH ((z-b)⁻¹) (hUmem z hz)) hi)
  · intro z hz
    change (B z)^Q.natDegree = _
    have hs := (IsAlgClosed.splits Q).natDegree_eq_card_roots
    have hzb : z-b ≠ 0 := by
      intro h
      exact (not_lt_of_ge hb) (sub_eq_zero.mp h ▸ hz)
    dsimp only [B]
    rw [mul_pow, hpow _ (hUmem z hz), (IsAlgClosed.splits Q).eval_eq_prod_roots_of_monic hQ, hs]
    rw [show (z-b) ^ Q.roots.card = (Q.roots.map (fun _ : ℂ => z-b)).prod by simp,
      ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    field_simp [hzb]
    <;> ring

end SpringerLean
