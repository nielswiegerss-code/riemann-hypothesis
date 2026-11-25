module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset

namespace Formalism.FT.SymmetricSeries

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

lemma prod_map_X_eq_monomial (s : Multiset σ) :
    (s.map (MvPolynomial.X : σ → MvPolynomial σ R)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

lemma toFinsupp_sum (s : Multiset σ) : ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, ih, Finsupp.single_apply]
    simp [add_comm]

lemma hsymm_eq_sum_monomial (k : ℕ) :
    MvPolynomial.hsymm σ R k =
      ∑ l ∈ finsuppAntidiag (univ : Finset σ) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  simp_rw [prod_map_X_eq_monomial]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact (Finset.mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by rw [toFinsupp_sum]; exact s.2, Finset.subset_univ _⟩
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    apply Subtype.ext
    simp
  · intro l _
    simp
  · intro s _
    rfl

open PowerSeries in
lemma geom_mul (a : R) : (1 - C a * X) * PowerSeries.mk (fun m => a ^ m) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [pow_succ, mul_comm]

end Formalism.FT.SymmetricSeries

namespace Formalism.FT.SymmetricSeries

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

open PowerSeries in
lemma coeff_prod_one_sub (i : ℕ) :
    coeff i (∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X)) =
      (-1) ^ i * MvPolynomial.esymm σ R i := by
  have h1 : ∏ j : σ, (1 - C (MvPolynomial.X j : MvPolynomial σ R) * X) =
      ∑ t ∈ (univ : Finset σ).powerset,
        C ((-1) ^ t.card * ∏ j ∈ t, (MvPolynomial.X j : MvPolynomial σ R)) * X ^ t.card := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, map_mul, map_pow,
      map_neg, map_one]
    ring

  rw [h1, map_sum]
  simp_rw [PowerSeries.coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  have hf : ((univ : Finset σ).powerset.filter fun t => i = t.card) = (univ : Finset σ).powersetCard i := by
    rw [Finset.powersetCard_eq_filter]
    ext t
    simp [eq_comm]
  rw [hf, MvPolynomial.esymm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_powersetCard.mp ht).2]

open PowerSeries in
lemma coeff_prod_geom (k : ℕ) :
    coeff k (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) =
      MvPolynomial.hsymm σ R k := by
  rw [PowerSeries.coeff_prod, hsymm_eq_sum_monomial]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [PowerSeries.coeff_mk]
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem esymm_hsymm_rel (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ range (k + 1), (-1) ^ i * MvPolynomial.esymm σ R i * MvPolynomial.hsymm σ R (k - i) = 0 := by
  have hAB : (∏ j : σ, (1 - PowerSeries.C (MvPolynomial.X j : MvPolynomial σ R) * PowerSeries.X)) *
      (∏ j : σ, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial σ R) ^ m)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => geom_mul _
  have h := congrArg (PowerSeries.coeff k) hAB
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_one,
    ite_eq_right (by omega)] at h
  simp only [coeff_prod_one_sub, coeff_prod_geom] at h
  exact h

end Formalism.FT.SymmetricSeries
