module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem tie_Xa_mono (F : FlagG S r T) {a b : ℕ} (h : a ≤ b) : F.Xa a ≤ F.Xa b :=
  Submodule.span_mono (by rintro _ ⟨i, hi, rfl⟩; exact ⟨i, lt_of_lt_of_le hi h, rfl⟩)

theorem tie_e_mem_Xa (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) :=
  Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

theorem tie_Xa_eq (F : FlagG S r T) (F' : FlagG S r T') (h : ∀ a, F'.e a - F.e a ∈ F.Xa a.val) (j : ℕ) :
    F'.Xa j = F.Xa j := by
  have h1 : ∀ j, F'.Xa j ≤ F.Xa j := by
    intro j
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F'.e a = (F'.e a - F.e a) + F.e a := by abel
    rw [h2]
    exact Submodule.add_mem _ (tie_Xa_mono F (le_of_lt ha) (h a)) (tie_Xa_mono F ha (tie_e_mem_Xa F a))
  refine le_antisymm (h1 j) ?_
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have h2 : F.e a = F'.e a - (F'.e a - F.e a) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (tie_Xa_mono F' ha (tie_e_mem_Xa F' a))
      (tie_Xa_mono F' (le_of_lt ha) (ih a.val ha (h a)))

theorem tie_X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.X FlagG.Xa
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, a.isLt, rfl⟩
  · rintro ⟨a, _, rfl⟩; exact ⟨a, rfl⟩

end Gen

end Formalism.MainNotions.BridgeLemma
