module

public import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

@[expose] public section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem class_map_naturality_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.LiftingTheory.adm21 D HW F := by
  intro l _ K s LL hg
  obtain ⟨hA, -, hN⟩ := h l K s LL hg
  refine ⟨hN, fun _ hl => ?_⟩
  intro T T' f pr pr' hpr
  have h2 : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg) = 2 →
      ∃ i : (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg).K, i ^ 2 = -1 := by
    intro h2
    exact absurd (((D.loc l).PD_p K).symm.trans h2) hl
  exact ((hA h2 T).2.2 T' f pr pr' hpr).symm

end Formalism.MainNotions.N
