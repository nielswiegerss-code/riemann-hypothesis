module

import Mathlib.RingTheory.Flat.TorsionFree
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators

@[expose] public section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem zl_WCb_injective : Function.Injective (algebraMap ℤ_[l] (WCb l)) := by
  change Function.Injective (zlW l (Cb l))
  unfold zlW
  rw [RingHom.coe_comp]
  exact (WittVector.map_injective _ (ZMod.castHom (dvd_refl l) (Cb l)).injective).comp
    (WittVector.equiv l).symm.injective

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
