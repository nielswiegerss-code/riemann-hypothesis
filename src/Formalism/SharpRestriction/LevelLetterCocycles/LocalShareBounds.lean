module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

namespace Formalism.MainNotions.N.LocalShareBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Polynomial Filter Topology

variable {D : D7}

theorem wtOf_off (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp


end Formalism.MainNotions.N.LocalShareBounds
