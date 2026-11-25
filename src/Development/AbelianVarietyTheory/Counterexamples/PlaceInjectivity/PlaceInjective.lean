module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField MeasureTheory

namespace GlobalTheory.VolRatioCheck

theorem embOf_mem (D : D7) (ρ : D.what₂.Tau) :
    embOf D ρ ∈ D.host.cmType :=
  ((factEmb D.R D.host).2 _).2 (D.eTau ρ).2

theorem place_injective (D : D7) :
    Function.Injective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  intro ρ ρ' h
  have hb := (factEmb D.R D.host).1
  rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
  · exact D.eTau.injective (Subtype.ext (hb.1 h1))
  · exfalso
    have e1 := embOf_mem D ρ
    have e2 := embOf_mem D ρ'
    rw [← h1] at e2
    exact (D.host.der.cmType.1 _).1 e1 e2

theorem place_bijective (D : D7) :
    Function.Bijective fun ρ : D.what₂.Tau => InfinitePlace.mk (embOf D ρ) := by
  have h1 : Nat.card D.what₂.Tau = D.R.f := by
    rw [Nat.card_congr D.eTau]; exact (factCardPsi D.R D.host).1
  have h2 : Nat.card (InfinitePlace D.host.E) = D.R.f := by
    rw [Nat.card_eq_fintype_card]; exact fDeg_host D
  exact (place_injective D).bijective_of_nat_card_le (by omega)

end GlobalTheory.VolRatioCheck
