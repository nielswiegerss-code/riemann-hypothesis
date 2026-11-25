module

public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl

@[expose] public section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem splitsF_of_splitsE (D : D7) (p : ℕ) (hp : p.Prime) (h : S.SplitsE D p) : StandardLattice.SplitsF D p := by
  have hF := BridgeLemma.splitsCompl_down D.host.F D.host.E p hp h
  refine ⟨?_, fun v hv => ?_⟩
  · exact (Nat.card_coe_set_eq _).trans ((BridgeLemma.ncard_plOver D.host.F hp hF).trans (finrank_F_eq D))
  · simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using (hF v.asIdeal v.isMaximal hv).1

end Formalism.MainNotions.J
