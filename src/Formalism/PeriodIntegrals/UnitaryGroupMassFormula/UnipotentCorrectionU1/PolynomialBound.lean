module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolyBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

open Matrix
open scoped ComplexConjugate

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

theorem polynomial_bound : PolyB := by
  intro k r κ P hP
  obtain ⟨hsmooth, hbound⟩ := pb_poly hP
  refine ⟨hsmooth, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hbound n
  refine ⟨C, fun u v hu hv hn g hg => ?_⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  have hw : ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v, B.unitLie k r x.2 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hu X hX
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hv X hX
  have hlen : (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ n := by
    simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR] using hn
  simpa using hC _ hw hlen g hg

end PI.UnitaryCorollaryDerivatives
