module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

theorem norm_inverse_bound : Formalism.FourierDecayAlt.ThreeDimData.NormInv := fun k r =>
  ⟨(Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).2, (Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1⟩

end Formalism.FourierDecayAlt.P
