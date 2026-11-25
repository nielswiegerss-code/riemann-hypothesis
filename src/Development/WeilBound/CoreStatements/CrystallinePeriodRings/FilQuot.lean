module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

namespace PositivityTheory.LocInh

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem filq_ker_eq : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l) :=
  (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

theorem filq_tie_fil (T : LocTied6 l P AI) (K : FinExt l) (n : ℕ) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) :
    x ∈ (P.PD K).Fil (n : ℤ) ↔ y ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [T.fil, h, fil_nat]

end SlopeTestRemainingChoices

end PositivityTheory.LocInh
