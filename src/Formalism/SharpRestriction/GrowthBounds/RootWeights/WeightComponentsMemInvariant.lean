module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightComponentsMemInvariant
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalRep
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem weight_components_mem_invariant [CharZero K] (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W)
    (s : Finset (Fin n → ℤ)) : ∀ f : (Fin n → ℤ) → V, (∀ mu ∈ s, f mu ∈ weightSp E mu) →
      ∑ mu ∈ s, f mu ∈ W → ∀ mu ∈ s, f mu ∈ W :=
  _root_.UpperTheory.Reformulated.B.Qf7.weight_components_mem_invariant E W hW s

theorem weightSpace_independent [CharZero K] (E : GLOps n K V) : iSupIndep (weightSp E) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv h0 i hi
  have := weight_components_mem_invariant E ⊥ (fun a x hx => by simp [(Submodule.mem_bot K).1 hx]) s v hv (by simp [h0]) i hi
  simpa using this

variable (E : GLOps n K V) (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W)

@[simp] theorem restricted_operator_coe (a b : Fin n) (x : W) : ((restrictStableOperators E W h a b x : W) : V) = E a b x := rfl

theorem restricted_mem_weightSpace_iff (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diagonal_rep, mem_weightSpace_iff_diagonal_rep]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff]
  simp

end Formalism.MainNotions.G.GLWeightTheory
