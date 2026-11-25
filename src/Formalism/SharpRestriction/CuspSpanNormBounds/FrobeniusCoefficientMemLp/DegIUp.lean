module

public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

namespace Formalism.MainNotions.S.Pv.DegI

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.MainNotions.PlaceDegreeData MeasureTheory
open scoped InnerProductSpace ENNReal

theorem minpq_pos (D : D7) : 1 ≤ min (pOf (epsSH D.R)) (qOf (epsSH D.R)) := by
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hq : min (PlaceDegreeData.pOf (epsSH D.R)) (PlaceDegreeData.qOf (epsSH D.R)) = D.R.rS + 1 := by
    rw [← epsilon_signature_eq D, negative_count_of_sign_pattern _ _ hk1]
    exact min_eq_right (positive_count_of_sign_pattern _ _ hk1)
  rw [hq]; omega




end Formalism.MainNotions.S.Pv.DegI
