module

public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeDistinctness
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC

namespace GlobalTheory.DefiniteBCFrozen

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem isBC_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {B : NBC A} {j : ℕ} {π : B.AU j} {Pa : List (Part A.CG)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa) : SphericalInertData.IsBC N A B j π Pa := by
  refine ⟨fun p hp => ⟨(h.discrete p hp).1, (h.discrete p hp).2, h.conjSelfDual p hp⟩, ?_, h.rank, h.split,
    h.inert, h.inf⟩
  refine h.distinct.map ?_
  rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ hh
  simp only [Prod.mk.injEq, Sigma.mk.injEq] at hh
  obtain ⟨⟨rfl, h2⟩, rfl⟩ := hh
  cases h2
  rfl

end GlobalTheory.DefiniteBCFrozen
