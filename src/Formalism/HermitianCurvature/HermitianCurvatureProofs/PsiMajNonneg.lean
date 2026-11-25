module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem gN_nonneg (g : Mx k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

end Formalism.FourierDecayAlt.P.S3dx6
