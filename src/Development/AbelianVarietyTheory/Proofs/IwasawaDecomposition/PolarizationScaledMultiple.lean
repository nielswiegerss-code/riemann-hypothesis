module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.TorRef.Scale

variable {X : Scheme.{0}}

theorem idlAlong_nsmul (D : EffCartierData X) (n : ℕ) {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) :
    idlAlong (D.nsmul n).idealSheaf ξ = idlAlong D.idealSheaf ξ ^ n := by
  obtain ⟨i, hi⟩ := D.exists_mem (ξ (IsLocalRing.closedPoint R))
  have h1 := (D.nsmul n).stalkId_idealSheaf i _ hi
  have h2 := D.stalkId_idealSheaf i _ hi
  have h3 : (X.presheaf.germ ((D.nsmul n).U i) (ξ (IsLocalRing.closedPoint R)) hi).hom ((D.nsmul n).f i) =
      ((X.presheaf.germ (D.U i) (ξ (IsLocalRing.closedPoint R)) hi).hom (D.f i)) ^ n :=
    map_pow _ _ _
  unfold idlAlong
  rw [h1, h3, h2, ← Ideal.map_pow, Ideal.span_singleton_pow]

end GlobalTheory.TorRef.Scale
