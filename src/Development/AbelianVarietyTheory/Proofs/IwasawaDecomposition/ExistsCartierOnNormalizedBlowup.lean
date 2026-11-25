module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory
