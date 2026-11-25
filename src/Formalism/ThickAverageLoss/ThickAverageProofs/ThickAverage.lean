module

public import Formalism.ThickAverageLoss.PartnersToFactorsAt
import Mathlib.Tactic.Lemma
import Formalism.JacobiWeightFamilies.Statement

@[expose] public section

open Finset

namespace Formalism.D5

open Formalism Formalism.WT

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

lemma zmod_two_cases_bis (x : ZMod 2) : x = 0 ∨ x = 1 := by
  first
    | (revert x; decide)

lemma zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

lemma zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
  decide

lemma phiSet_card : (PhiSet (H := H)).card = 2 * Fintype.card H := by
  have h1 : PhiSet (H := H) =
      (Finset.univ.filter (fun e : E0 => e.1 = 0)) ×ˢ (Finset.univ : Finset H) := by
    ext ⟨⟨a, b⟩, h⟩
    simp [PhiSet, InPhi]
  have h2 : (Finset.univ.filter (fun e : E0 => e.1 = 0)).card = 2 := by
    first
      | decide
  rw [h1, Finset.card_product, h2, Finset.card_univ]



lemma thick_filter (T2 : Finset H) (u0 t : H) :
    univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t) ∧ IsThickAt T2 u0 (cconj + g + topPl t))
      = T2.image (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  ext ⟨⟨a, b⟩, h⟩
  rcases zmod_two_cases_bis a with rfl | rfl <;> rcases zmod_two_cases_bis b with rfl | rfl <;>
    simp [InPhi, IsThickAt, topPl, cconj, thickPl, zmod_two_one_add_one, zmod_two_one_ne_zero.symm, sub_eq_iff_eq_add]

lemma thick_inj (u0 t : H) :
    Set.InjOn (fun s => ((((1 : ZMod 2), (0 : ZMod 2)), s + u0 - t) : E0 × H)) Set.univ := by
  intro x _ y _ hxy
  simpa using hxy


end

end Formalism.D5
