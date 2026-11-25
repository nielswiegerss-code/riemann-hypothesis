module

public import Formalism.SubspaceCounting.Statement
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

open scoped BigOperators

namespace Formalism.G0

namespace ManyOrbitsP

theorem add_pow_ge (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k ≤ (p + q) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpq : 0 ≤ p + q := add_nonneg hp hq
    have h1 := mul_le_mul_of_nonneg_left ih hpq
    have h2 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * p ^ k := by positivity
    have e : (p + q) * (p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k) -
        (p ^ (k + 1 + 1) + (((k : ℝ) + 1) + 1) * q * p ^ (k + 1)) = ((k : ℝ) + 1) * q ^ 2 * p ^ k := by
      ring
    have e2 : (p + q) * (p + q) ^ (k + 1) = (p + q) ^ (k + 1 + 1) := by ring
    push_cast
    linarith

theorem fact_esymm_le (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
      simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      have e : (a ::ₘ t).esymm (n + 1) = t.esymm (n + 1) + a * t.esymm n := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      have h1 := ih ht (n + 1)
      have h2 := ih ht n
      have h3 := add_pow_ge t.sum a hS ha n
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * a)
      rw [e, Multiset.sum_cons, add_comm a t.sum]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e5 : ((n : ℝ) + 1) * (n.factorial : ℝ) * (t.esymm (n + 1) + a * t.esymm n) =
          ((n : ℝ) + 1) * (n.factorial : ℝ) * t.esymm (n + 1) + ((n : ℝ) + 1) * a * ((n.factorial : ℝ) * t.esymm n) := by
        ring
      linarith [h1, h3, h4, e5]

section Mod

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem allBut_mono {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C, hCM, hcard.trans hg, fun x hx => ?_⟩
  have := Submodule.smul_mem _ (π ^ (E' - E)) (hC x hx)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hE] at this

end Mod

end ManyOrbitsP

end Formalism.G0
