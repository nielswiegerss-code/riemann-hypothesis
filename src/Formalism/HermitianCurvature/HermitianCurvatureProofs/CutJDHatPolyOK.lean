module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZinvBound
import Mathlib.Tactic.Linter.Style
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfUnitWords

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open scoped ContDiff

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

theorem jdh_pd_star {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) :
    U.IsPolyDeg κ (fun g => star (P g)) := by
  apply _root_.GlobalTheory.HatNF.polyOK_star <;> assumption

theorem polynomial_decay_admissible : JDPolyOK := by
  apply GlobalTheory.HatNF.polyOp_ok

end Formalism.FourierDecayAlt.P.CutMP
