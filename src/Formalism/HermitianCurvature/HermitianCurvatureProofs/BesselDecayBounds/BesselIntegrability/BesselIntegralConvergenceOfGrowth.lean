module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvPsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvSig
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.NonnegNormSums.IntegrandCont
import Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.IdempotentTranslateMeasurable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

theorem one_add_AG_lt_aOf {k r : ℕ} {h : ℝ} (hOK : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) :
    1 + Formalism.FourierDecayAlt.ThreeDimData.AG k r < Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by
  obtain ⟨-, -, -, h4⟩ := hOK
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    positivity
  have h0 : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem dsigW_eq_bessel_integrability {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (w : H), PI.UpqRep.dsigW (k := k) (r := r) σ W w = Formalism.MainNotions.S.dsigW σ W w
  | [], w => rfl
  | X :: W, w => by
    simp only [PI.UpqRep.dsigW, Formalism.MainNotions.S.dsigW]
    rw [dsigW_eq_bessel_integrability σ W w]
    rfl

end Formalism.FourierDecayAlt.P
