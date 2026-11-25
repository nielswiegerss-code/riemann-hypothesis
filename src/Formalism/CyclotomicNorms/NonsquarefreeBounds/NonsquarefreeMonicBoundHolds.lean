module

public import Formalism.CyclotomicNorms.StatementI
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma

@[expose] public section

open Finset Polynomial

namespace Formalism.CyclotomicNorms

namespace Sqf

variable {K : Type} [Field K]

lemma coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, ite_eq_right (Nat.ne_of_lt i.2), zero_add, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj => ite_eq_right (fun h => hj (Fin.ext h).symm)) (by simp)]
  simp

lemma coeff_monicOf_ge {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => ite_eq_right (by have := j.2; omega)), add_zero]

lemma natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]

lemma monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  unfold monicOf
  exact monic_X_pow_add (degree_sum_fin_lt a)

lemma monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    split_ifs with hn
    · subst hn
      rw [← hd]
      exact hp.coeff_natDegree.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Sqf

end Formalism.CyclotomicNorms
