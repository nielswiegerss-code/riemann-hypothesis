module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.FormalDegreeBessel.StatementG
public import Mathlib.Analysis.Matrix.Normed
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.StatementJF

@[expose] public section

open Matrix MeasureTheory Filter

namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  apply _root_.Formalism.FourierDecayAlt.P.Qx8.psi_one <;> assumption

end Formalism.FourierDecayAlt.P.BesselCapelliCommutation
