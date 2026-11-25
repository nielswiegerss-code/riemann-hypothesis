module

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.LocalRingCardinality.DataHost
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open NumberField IsDedekindDomain Filter Topology Asymptotics

namespace Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds

section Sum
variable (K : Type) [Field K] [NumberField K]

theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun w : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  apply PositivityTheory.Lord.summable_primes_rpow <;> assumption

end Sum

end Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds
