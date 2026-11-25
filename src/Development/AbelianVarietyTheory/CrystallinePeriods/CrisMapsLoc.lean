module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CrisMaps
open Formalism GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem phiA_eq (l : ℕ) [Fact l.Prime] : phiA l = frob l := rfl

theorem sigA_eq (g : Per.Gq l) : sigA g = gal g := rfl

theorem phiA_extends (l : ℕ) [Fact l.Prime] : Extends (Per.φA l) (phiA l) := by
  rw [phiA_eq]; exact frob_extends l

theorem sigA_extends (g : Per.Gq l) : Extends (Per.σA g) (sigA g) := by
  rw [sigA_eq]; exact gal_extends g

theorem phiA_sigA (g : Per.Gq l) (x : Per.Acris l) : phiA l (sigA g x) = sigA g (phiA l x) := by
  rw [phiA_eq, sigA_eq]; exact frob_gal g x

theorem φB_phiA (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) := by
  rw [phiA_eq]; exact φB_algebraMap l x

theorem σB_sigA (g : Per.Gq l) (x : Per.Acris l) :
    Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x) := by
  rw [sigA_eq]; exact σB_algebraMap g x

end GlobalTheory.CrisMaps
