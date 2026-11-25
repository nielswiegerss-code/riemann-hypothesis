module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Wt

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem operator_pow_shifts_weight {E : GLOps n K V} (hs : OperatorsShiftWeightsByRoots E) (a b : Fin n) (ν : Fin n → ℤ) (k : ℕ) (x : V)
    (hx : x ∈ weightSp E ν) : ((E a b) ^ k) x ∈ weightSp E (ν + (k : ℤ) • rootW a b) := by
  unfold OperatorsShiftWeightsByRoots at hs
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := hs a b _ _ ih
    convert h1 using 2
    rw [Nat.cast_succ, add_smul, one_smul, add_assoc]

end Wt

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem binomial_subring_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ binomialDiagonalSubring E) : ∀ x ∈ M, u x ∈ M := by
  unfold binomialDiagonalSubring at hu
  unfold UZStable at hM
  induction hu using Subring.closure_induction with
  | mem u hu => obtain ⟨a, k, rfl⟩ := hu; exact hM _ (Or.inr ⟨a, k, rfl⟩)
  | zero => intro x _; simp
  | one => intro x hx; simpa using hx
  | add u v _ _ hu hv => intro x hx; rw [LinearMap.add_apply]; exact M.add_mem (hu x hx) (hv x hx)
  | neg u _ hu => intro x hx; rw [LinearMap.neg_apply]; exact M.neg_mem (hu x hx)
  | mul u v _ _ hu hv => intro x hx; rw [Module.End.mul_apply]; exact hu _ (hv x hx)

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
