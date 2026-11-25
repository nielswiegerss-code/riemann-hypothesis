module

public import Formalism.PeriodIntegrals.BesselMapUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

set_option linter.unusedVariables false

namespace Formalism.MainNotions.BridgeCS3d

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih =>
    show PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW (k := k) (r := r) σ w v) =
      Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)
    rw [ih]
    rfl

theorem isBesselMapSm_iff {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ)
    (ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (l : H → Wp) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π l ↔
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l := by
  simp only [PI.BesselMapUniq.IsBesselMapSm, Formalism.MainNotions.S.IsBesselMapSm, PI.BesselMapUniq.IsCWCont,
    Formalism.MainNotions.S.IsCWCont, dsigW_eq]
  exact Iff.rfl

end Formalism.MainNotions.BridgeCS3d
