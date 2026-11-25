module

public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

end GlobalTheory.TorRef
