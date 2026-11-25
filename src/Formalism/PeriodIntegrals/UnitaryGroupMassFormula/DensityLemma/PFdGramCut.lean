module

public import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.BigCellVanishingOfCommute

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

namespace PI.UnitaryGroupMassFormula.DLm.Gram

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  simp [UWset, UH]

end

end PI.UnitaryGroupMassFormula.DLm.Gram
