module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem Q_nonneg (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 0 ≤ Q χ := by
  by_cases hχ : χ = 0
  · rw [hχ, Q_zero hϖ (D := D) (Q := Q) (hQ := hQ)]
  · exact le_trans zero_le_one (Q_pos hϖ (D := D) (Q := Q) (hQ := hQ) hχ)

end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
