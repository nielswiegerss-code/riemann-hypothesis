module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

end GlobalTheory.TorRef
