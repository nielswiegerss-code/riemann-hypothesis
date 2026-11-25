module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  apply _root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.gf_cont <;> assumption

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses
