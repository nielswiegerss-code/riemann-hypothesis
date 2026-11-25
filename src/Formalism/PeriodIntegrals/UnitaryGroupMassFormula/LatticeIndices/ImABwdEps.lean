module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGNonunit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAPsiVScPSame

@[expose] public section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_eps'_eq (p : TypX X) :
    1 - epsP X p = PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) := by
  have h := imA_ew_split X p
  rw [epsP]
  linear_combination -h

theorem imA_bw_eps (p : TypX X) (i : Fin D.R.k) :
    epsP X p • PI.FinKW.vecV X.B.I p.1 (X.bw i) = PI.FinKW.vecV X.B.I p.1 (X.bw i) := by
  conv_rhs => rw [X.bw_w i]
  rw [imA_vecV_smul']

end MassDataIdxSteps
