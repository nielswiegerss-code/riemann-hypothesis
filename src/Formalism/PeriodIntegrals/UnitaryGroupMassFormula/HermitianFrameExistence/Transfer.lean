module

public import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen

@[expose] public section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

theorem hJ_rv (I : Formalism.MainNotions.S.AutInst) (v : NumberField.InfinitePlace I.F) (x y : Fin I.n → I.E) :
    hJ (I.ε v) (rv I v x) (rv I v y) = I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  apply _root_.PI.ScMuExists.UnitaryGroupMassFormula.rv_hJ <;> assumption

end PI.ScPiFrameW
