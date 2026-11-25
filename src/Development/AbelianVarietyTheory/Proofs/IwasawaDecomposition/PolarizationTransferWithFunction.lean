module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolDiv

theorem idlAlong_fromSpecStalk {X : Scheme.{0}} (I : X.IdealSheafData) (x : X) {W : Type} [CommRing W] [IsLocalRing W]
    (g : X.presheaf.stalk x →+* W) :
    idlAlong I (Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x) = (FinalTheorems.stalkId I x).map g := by
  obtain ⟨⟨U, hU⟩, hx, -⟩ := EffCartierData.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have e0 : ∀ (y : X) (hy : y ∈ U), X.fromSpecStalk y = Spec.map (X.presheaf.germ U y hy) ≫ hU'.fromSpec :=
    fun y hy => (hU'.fromSpecStalk_eq_fromSpecStalk hy).symm
  generalize hχ : Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecStalk x = χ
  have e1 : χ = Spec.map (X.presheaf.germ U x hx ≫ CommRingCat.ofHom g) ≫ hU'.fromSpec := by
    rw [← hχ, e0 x hx]
    exact (Spec.map_comp_assoc (X.presheaf.germ U x hx) (CommRingCat.ofHom g) hU'.fromSpec).symm
  have hc : χ (closedPoint W) ∈ U := by
    have : χ (closedPoint W) ∈ Set.range hU'.fromSpec :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun f => f (closedPoint W)) e1.symm)⟩
    rwa [hU'.range_fromSpec] at this
  have e2 : χ = Spec.map (X.presheaf.germ U _ hc ≫ Scheme.stalkClosedPointTo χ) ≫ hU'.fromSpec := by
    rw [Spec.map_comp, Category.assoc, ← e0 _ hc]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ).symm
  have e3 := Spec.map_injective ((cancel_mono hU'.fromSpec).1 (e1.symm.trans e2))
  unfold idlAlong
  rw [ds_stalkId_eq_map I ⟨U, hU⟩ _ hc, ds_stalkId_eq_map I ⟨U, hU⟩ x hx, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← e3]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end GlobalTheory.PolDiv
