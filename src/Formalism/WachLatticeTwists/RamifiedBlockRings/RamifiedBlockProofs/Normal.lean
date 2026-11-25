module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Formalism.CharacterColumnKernels.Statement
import Formalism.TruncatedSeriesCounting.LemmaDetPoly
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

open Module

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Normal

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hsurj : Function.Surjective (Submodule.linearProjOfIsCompl p q h) :=
    fun x => ⟨(x : r → O), Submodule.linearProjOfIsCompl_apply_left h x⟩
  have hfin : Module.Finite O p := Module.Finite.of_surjective _ hsurj
  haveI : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  haveI : Module.FinitePresentation O p := by
    first
    | exact Module.finitePresentation_of_projective _ _
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let E : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hE : IsIdempotentElem E := by
    have h : E * E = E := by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]
    exact h
  have hC : IsCompl (LinearMap.range E) (LinearMap.ker E) := LinearMap.IsIdempotentElem.isCompl hE
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC.symm
  let bR := Module.Free.chooseBasis O (LinearMap.range E)
  let bK := Module.Free.chooseBasis O (LinearMap.ker E)
  let B := (bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hC)
  let σ := B.indexEquiv (Pi.basisFun O r)
  let B' := B.reindex σ
  have key : ∀ j, E (B' j) = (if (σ.symm j).isLeft then 1 else 0 : O) • B' j := by
    intro j
    simp only [B', Module.Basis.reindex_apply]
    rcases σ.symm j with a | b
    · have hm : (B (Sum.inl a)) ∈ LinearMap.range E := by
        simp [B, Module.Basis.prod_apply]
      simpa using ((LinearMap.IsIdempotentElem.mem_range_iff hE).mp hm)
    · have hm : (B (Sum.inr b)) ∈ LinearMap.ker E := by
        simp [B, Module.Basis.prod_apply]
      simpa using hm
  refine ⟨(Pi.basisFun O r).toMatrix B', B'.toMatrix (Pi.basisFun O r),
    fun j => if (σ.symm j).isLeft then 1 else 0, fun j => by dsimp only; split_ifs <;> simp,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hEP : e * (Pi.basisFun O r).toMatrix B' = (Pi.basisFun O r).toMatrix B' *
      Matrix.diagonal (fun j => if (σ.symm j).isLeft then 1 else 0) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (key j) i
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this, mul_comm]
  calc e = e * ((Pi.basisFun O r).toMatrix B' * B'.toMatrix (Pi.basisFun O r)) := by
        rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hEP]

theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  haveI : Nontrivial O := f.domain_nontrivial
  have hmap : (P * Matrix.diagonal d * Q).map f = P.map f * Matrix.diagonal (fun j => f (d j)) * Q.map f := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]
  have h1 : P.map f * Q.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hPQ
  have h2 : Q.map f * P.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hQP
  have hPu : IsUnit (P.map f).det := Matrix.isUnit_det_of_right_inverse h1
  have hQu : IsUnit (Q.map f).det := Matrix.isUnit_det_of_right_inverse h2
  rw [hmap, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu,
    Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun j => by rcases hd j with h | h <;> simp [h]


end Normal


end Formalism.RepresentationBoundsCohomology.ringDataObjects
