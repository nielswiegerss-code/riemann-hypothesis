module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions Formalism.BasicNotions.TH

theorem halfInt_of_integrality (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hu : Formalism.QuantumDeterminants.IsHCParam u) (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) : HalfIntegralDifference k r u v b := by
  intro i s
  obtain ⟨m1, e1⟩ := hu.2 i
  obtain ⟨m2, e2⟩ := hl.2 s
  refine ⟨m1 - m2 - r - 1, ?_⟩
  push_cast at e1 e2 ⊢
  linarith

end Formalism.MainNotions.LeviCoordinates
