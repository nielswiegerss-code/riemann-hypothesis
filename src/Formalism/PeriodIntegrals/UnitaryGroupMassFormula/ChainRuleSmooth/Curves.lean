module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed
import Formalism.HermitianCurvature.StatementB
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

@[expose] public section

open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff

namespace CCRuleCW

open Formalism.FourierDecayAlt

theorem entry_hasDerivAt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  apply _root_.Formalism.MainNotions.S.Gauge.exp_entry <;> assumption

end CCRuleCW
