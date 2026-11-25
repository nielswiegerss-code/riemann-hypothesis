module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem E_mem_span_l_X (bk : BK K) : bk.E ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hc : constantCoeff bk.E = (l : Wq l bk.a) * w := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
  rw [eq_shift_mul_X_add_const bk.E, hc, map_mul, map_natCast]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end GlobalTheory.BSP.BK

theorem GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ),
    ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S,
      (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  intro l _ K bk N
  refine ⟨N, fun m => ⟨N + (m + bk.Ep.natDegree * N), fun s hs => ?_⟩⟩
  have hJ : bk.J ≤ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} :=
    sup_le le_sup_left (Ideal.span_singleton_le_iff_mem _ |>.2 (BK.E_mem_span_l_X bk))
  have h1 : bk.J ^ (N + (m + bk.Ep.natDegree * N)) ≤
      Ideal.span {(l : bk.S) ^ N} ⊔ Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)} := by
    refine (Ideal.pow_right_mono hJ _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {(X : bk.S)})
      (n := N) (m := m + bk.Ep.natDegree * N)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
  have hs' := (sup_le h1 le_sup_left : _ ≤ Ideal.span {(l : bk.S) ^ N} ⊔
      Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)}) hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  set t := s - (X : bk.S) ^ (bk.Ep.natDegree * N) * g with ht
  have htm : (X : bk.S) ^ m * t = C ((l : Wq l bk.a) ^ N) * h := by
    rw [ht, map_pow, map_natCast, mul_sub, ← hyz]; ring
  have ht' : t = C ((l : Wq l bk.a) ^ N) * PowerSeries.mk (fun k => coeff (k + m) h) := by
    ext k
    have := congrArg (coeff (k + m)) htm
    rw [coeff_X_pow_mul', ite_eq_left (Nat.le_add_left m k), Nat.add_sub_cancel, coeff_C_mul] at this
    rw [this, coeff_C_mul, coeff_mk]
  have hs2 : s = ((X : bk.S) ^ bk.Ep.natDegree) ^ N * g + (l : bk.S) ^ N * PowerSeries.mk (fun k => coeff (k + m) h) := by
    have : s = t + (X : bk.S) ^ (bk.Ep.natDegree * N) * g := by rw [ht]; ring
    rw [this, ht', map_pow, map_natCast, ← pow_mul]; ring
  rw [hs2]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (GlobalTheory.BSP.BK.X_pow_natDegree_mem_J bk) N))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) N))
