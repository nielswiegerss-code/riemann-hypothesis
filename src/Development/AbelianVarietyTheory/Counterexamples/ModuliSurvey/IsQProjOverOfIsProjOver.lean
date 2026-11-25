module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

namespace GlobalTheory.SchemeWords

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Proj
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}

open AlgebraicGeometry CategoryTheory IsLocalRing in
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} in
theorem _root_.GlobalTheory.SchemeWords.isProper_of_isProjOver (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : IsProper f :=
  _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper R X f h

open AlgebraicGeometry CategoryTheory IsLocalRing in
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} in
theorem _root_.GlobalTheory.SchemeWords.isQProjOver_of_isProjOver (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  exact ⟨N, i, inferInstance, inferInstance, rfl⟩


open AlgebraicGeometry CategoryTheory IsLocalRing in
variable {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} in
theorem _root_.GlobalTheory.SchemeWords.isProjOver_iff : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f ↔ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f ∧ IsProper f := by
  refine ⟨fun h => ⟨_root_.GlobalTheory.SchemeWords.isQProjOver_of_isProjOver h, _root_.GlobalTheory.SchemeWords.isProper_of_isProjOver h⟩, ?_⟩
  rintro ⟨⟨N, i, hi, hq, rfl⟩, hp⟩
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  haveI : IsProper i := IsProper.of_comp i (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N)
  exact ⟨N, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, rfl⟩

end Proj

end GlobalTheory.SchemeWords
