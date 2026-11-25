module

public import Formalism.TruncatedSeriesCounting.LemmaDetPoly
import Mathlib.Tactic.TypeStar

@[expose] public section

open Finset Classical

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Blocks
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)

theorem blk_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (c : α) :
    (M * N).toSquareBlock bl c = M.toSquareBlock bl c * N.toSquareBlock bl c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  have h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0,
    add_zero]

end Blocks

theorem r_mem {O : Type} [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d O)) (g : G) : r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp


end Formalism.RepresentationBoundsCohomology.ringDataObjects
