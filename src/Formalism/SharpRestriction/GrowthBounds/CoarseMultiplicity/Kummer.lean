module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem multinomial_val (p : ℕ) {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha,
      Nat.add_sub_cancel]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have h1 := @Nat.factorization_choose_le_log p (f a + ∑ i ∈ s, f i) (f a)
      have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.log_mono_right (Nat.le_add_left _ _)
      obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, (Nat.succ_pred_eq_of_pos hs.card_pos).symm⟩
      rw [hk, Nat.add_sub_cancel] at ih
      rw [hk, add_mul, one_mul]
      have h3 := ih.trans (Nat.mul_le_mul_left k h2)
      omega

theorem expFact_eq {ι : Type*} [Fintype ι] {n : ℕ} (μ : ι × Fin n →₀ ℕ) :
    expFact μ = ∏ x : ι, ∏ c : Fin n, (μ (x, c)).factorial := by
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem expFact_mul {ι : Type*} [Fintype ι] {n : ℕ} (p : ℕ) (d : ι → ℕ) (μ : ι × Fin n →₀ ℕ)
    (hμ : ∀ x, multideg μ x = d x) :
    ∃ M : ℕ, M ≠ 0 ∧ expFact μ * M = ∏ x, (d x).factorial ∧
      M.factorization p ≤ ∑ x, (n - 1) * Nat.log p (d x) := by
  classical
  refine ⟨∏ x : ι, Nat.multinomial Finset.univ (fun c : Fin n => μ (x, c)), ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun x _ => (Nat.multinomial_pos _ _).ne'
  · rw [expFact_eq, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Nat.multinomial_spec, ← hμ x]
    rfl
  · rw [Nat.factorization_prod fun x _ => (Nat.multinomial_pos _ _).ne', Finsupp.finsetSum_apply]
    refine Finset.sum_le_sum fun x _ => ?_
    have := multinomial_val p Finset.univ (fun c : Fin n => μ (x, c))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← hμ x]
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
