module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Mathlib.Algebra.Order.Star.Rat
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace Formalism.MainNotions.S.Inh

section

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB

theorem amp_isHCParam_lamSH (R : Ranks) (P : HCParam R) : IsHCParam (lamSH R P) := by
  apply _root_.GlobalTheory.Mem.Vol.lamSH_isHCParam <;> assumption

theorem amp_isHCParam_lamD (D : D7) (τ : D.what₂.Tau) : IsHCParam (lamD D τ) := amp_isHCParam_lamSH D.R (D.hc τ)

end

end Formalism.MainNotions.S.Inh
