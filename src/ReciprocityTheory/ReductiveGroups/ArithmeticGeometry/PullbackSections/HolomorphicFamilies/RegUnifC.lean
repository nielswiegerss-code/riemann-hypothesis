module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

variable (D : DegPre R)

section Descent

open IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_hasVal {ϖ : V} (hϖ : Irreducible ϖ) (x : FractionRing V) (hx : x ≠ 0) : ∃ n : ℤ, HasVal ϖ x n := by
  apply ReciprocityTheory.ChartRestriction.G.DVR.hasVal_of_ne_zero <;> assumption

variable {D : DegData V (maximalIdeal V)} (F : Type) [Field F] [Algebra (FractionRing V) F]

end Descent

end ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC
