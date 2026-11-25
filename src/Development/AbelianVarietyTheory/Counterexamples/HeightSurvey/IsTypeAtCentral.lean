module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.TypeAtTest

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isTypeAt_zero {τ : D.what₂.Tau} {S : SPar} : IsTypeAt θ V τ S 0 ↔
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ := by
  constructor
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, -⟩
    exact ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
    refine ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, fun x => ⟨fun _ => 0, fun i => ?_, fun _ => 0,
      fun i => ?_, ⟨[], fun _ => 0, by simp, fun i w _ => by simp, fun S' _ => by simp,
        ⟨fun _ => 0, continuous_const, fun g _ w _ => by simp⟩⟩, fun g _ => by simpa using hasSum_zero⟩⟩
    · intro k Xs _
      simp only [map_zero]
      exact contDiff_const
    · exact ⟨[], 0, by simp, fun w _ => by simp⟩

end GlobalTheory.TypeAtTest
