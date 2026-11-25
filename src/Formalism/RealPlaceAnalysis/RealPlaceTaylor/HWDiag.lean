module

public import Formalism.RealPlaceAnalysis.StatementB
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

open Finset

namespace Formalism.REAL

private theorem epow_zero_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin n) : epow E 0 a b = if a = b then 1 else 0 := by
  first | rfl

private theorem epow_succ_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (k : ℕ) (a b : Fin n) : epow E (k + 1) a b = ∑ c, epow E k a c * E c b := by
  first | rfl

theorem HWDiag_cov {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) :
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0) := by
  intro k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow]
    have lhs : E c d * (if a = b then (1:A) else 0) - (if a = b then (1:A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [lhs]
    by_cases h : d = a ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h1 : (if d = a then (if c = b then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      have h2 : (if b = c then (if a = d then (1:A) else 0) else 0) = 0 := by
        split_ifs with h2 h3 <;> simp_all
      rw [h1, h2, sub_zero]
  | succ k ih =>
    intro a b c d
    have key : ∀ e, E c d * (epow E k a e * E e b) - (epow E k a e * E e b) * E c d
        = (E c d * epow E k a e - epow E k a e * E c d) * E e b
          + epow E k a e * (E c d * E e b - E e b * E c d) := by
      intro e; noncomm_ring
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun e _ => key e)]
    simp only [ih, hE c d]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul,
        mul_ite] <;> abel

private theorem module_end_mul_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f g : Module.End ℂ V) (v : V) : (f * g) v = f (g v) := rfl

theorem HWDiag_covApply {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (k : ℕ) (a b c d : Fin n) (v : V) :
    epow E k a b (E c d v) = E c d (epow E k a b v) -
      ((if d = a then epow E k c b v else 0) - (if b = c then epow E k a d v else 0)) := by
  have h := congrArg (fun f : Module.End ℂ V => f v) (HWDiag_cov E hE k a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h' : epow E k a b (E c d v) = E c d (epow E k a b v) -
      (E c d (epow E k a b v) - epow E k a b (E c d v)) := by abel
  rw [h', h]
  split_ifs <;> simp

theorem HWDiag_upper {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hE : GlRel E)
    (hv : IsHW E ν v) : ∀ (k : ℕ) (a b : Fin n), a < b → epow E k a b v = 0 := by
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  intro k
  induction k with
  | zero =>
    intro a b hab
    simp [epow_zero_apply, hab.ne]
  | succ k ih =>
    intro a b hab
    rw [epow_succ_apply, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [module_end_mul_apply]
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · rw [hv'.2 c b hcb, map_zero]
    · rw [hcb, hv'.1 b, map_smul, ih a b hab, smul_zero]
    · rw [HWDiag_covApply E hE k a c c b v, ih a c (hab.trans hcb), map_zero,
        ih a b hab]
      simp [hab.ne']

private theorem card_filter_fin_lt_eq {n : ℕ} (a : Fin n) :
    (univ.filter fun b : Fin n => a < b).card = n - 1 - (a : ℕ) := by
  first
  | (rw [show (univ.filter fun b : Fin n => a < b) = Finset.Ioi a by ext; simp]
     exact Fin.card_Ioi a)

private theorem cast_nat_sub_one_sub_fin_eq_complex {n : ℕ} (a : Fin n) :
    ((n - 1 - (a : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (a : ℂ) := by
  have ha := a.isLt
  have hN : n - 1 - (a : ℕ) + (a : ℕ) + 1 = n := by omega
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℂ) + (a : ℂ) + 1 = (n : ℂ) := by
    first
    | exact_mod_cast hN
  linear_combination hc

theorem generatorPowDiagRecursion_holds : HWDiag := by
  unfold HWDiag
  intro V _i1 _i2 n E ν v hE hv k a
  have hv' : (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0 := hv
  have hterm : ∀ c : Fin n, epow E k a c (E c a v) =
      (if c = a then ν a • epow E k a a v else 0) +
        (if a < c then epow E k a a v - epow E k c c v else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hca
    · rw [hv'.2 c a hca, map_zero]
      simp [hca.ne, not_lt.mpr hca.le]
    · rw [hca, hv'.1 a, map_smul]
      simp
    · rw [HWDiag_covApply E hE k a c c a v,
        HWDiag_upper E ν v hE hv k a c hca, map_zero]
      simp [hca.ne', hca]
  have h1 : (∑ c : Fin n, if c = a then ν a • epow E k a a v else 0) =
      ν a • epow E k a a v := by
    simp
  have h2 : (∑ c : Fin n, if a < c then epow E k a a v - epow E k c c v else 0) =
      ∑ c ∈ univ.filter (fun b => a < b), (epow E k a a v - epow E k c c v) := by
    rw [Finset.sum_filter]
  have hsmul : (n - 1 - (a : ℕ)) • epow E k a a v =
      ((n : ℂ) - 1 - (a : ℂ)) • epow E k a a v := by
    rw [← cast_nat_sub_one_sub_fin_eq_complex a]
    first
    | exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
  rw [epow_succ_apply, LinearMap.sum_apply]
  simp only [module_end_mul_apply, hterm]
  rw [Finset.sum_add_distrib, h1, h2, Finset.sum_sub_distrib, Finset.sum_const,
    card_filter_fin_lt_eq, hsmul]
  simp only [lsh, add_smul]
  abel

end Formalism.REAL
