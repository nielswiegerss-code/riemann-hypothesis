module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.IndexWeightsDominance
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace DominanceOrderLemmas

theorem domLe_refl {n : ℕ} (ν : Fin n → ℤ) : DomLe ν ν := ⟨rfl, fun _ => le_rfl⟩

theorem domLe_trans {n : ℕ} {a b c : Fin n → ℤ} (h1 : DomLe a b) (h2 : DomLe b c) : DomLe a c :=
  ⟨h1.1.trans h2.1, fun j => (h1.2 j).trans (h2.2 j)⟩

theorem vars_of_polB {R : Type*} [CommRing R] {n N : ℕ} {B : ℕ → ℕ} {G : MvPolynomial (ℕ × Fin n) R}
    (hG : G ∈ polB R n N B) : ∀ x ∈ G.vars, x.1 < N := by
  intro x hx
  by_contra! hlt
  have hGi := (Submodule.mem_iInf _).mp hG x.1
  rw [ite_eq_right (not_lt.mpr hlt), mem_weightedHomogeneousSubmodule] at hGi
  obtain ⟨e, he, hex⟩ := (MvPolynomial.mem_vars_iff_mem_support x).mp hx
  have h0 := hGi (mem_support_iff.mp he)
  have hpos : 0 < e x := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hex)
  rw [Finsupp.weight_apply, Finsupp.sum] at h0
  have hle := Finset.single_le_sum (f := fun y => e y • (if y.1 = x.1 then 1 else 0 : ℕ))
    (fun _ _ => Nat.zero_le _) hex
  simp only [ite_true, smul_eq_mul, mul_ite, mul_one, mul_zero] at hle h0
  omega

theorem actAll_X {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L)
    (i : ℕ) (a : Fin n) :
    actAll isVec g gi (X (i, a)) =
      if isVec i then ∑ b, X (i, b) * C (g b a) else ∑ b, X (i, b) * C (gi a b) := by
  unfold actAll
  rw [aeval_X]
  split_ifs <;> simp [Matrix.vecMul, dotProduct]

theorem vars_actX {L : Type*} [CommRing L] [Nontrivial L] {n : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) (x : ℕ × Fin n) :
    ∀ y ∈ (actAll isVec g gi (X x)).vars, y.1 = x.1 := by
  intro y hy
  rw [actAll_X] at hy
  split_ifs at hy <;>
  · obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hy)
    have h' := MvPolynomial.vars_mul _ _ hb
    rw [Finset.mem_union, vars_X, vars_C] at h'
    simp only [Finset.mem_singleton, Finset.notMem_empty, or_false] at h'
    rw [h']

theorem vars_act {L : Type*} [CommRing L] [Nontrivial L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < N) :
    ∀ y ∈ (actAll isVec g gi P).vars, y.1 < N := by
  intro y hy
  have heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P := by
    simp only [actAll, bind₁, aeval_X]
  rw [heq] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)
  rw [vars_actX isVec g gi x y hyx]
  exact hv x hx

end DominanceOrderLemmas

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
