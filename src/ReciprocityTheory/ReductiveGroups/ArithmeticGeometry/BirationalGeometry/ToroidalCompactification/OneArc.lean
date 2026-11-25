module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArcSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  exact Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem val_exists {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] {X S : Scheme.{0}} (s : X ⟶ S) [IsProper s]
    (y : Sp (FractionRing R) ⟶ X) (r : Sp R ⟶ S) (h : y ≫ s = Out.jK R ≫ r) :
    ∃ x : Sp R ⟶ X, Out.jK R ≫ x = y ∧ x ≫ s = r := by
  obtain ⟨hE, -⟩ : ValuativeCriterion.Existence s ∧ QuasiCompact s := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) s := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact this
  obtain ⟨⟨l⟩⟩ := hE ⟨R, FractionRing R, y, r, ⟨h⟩⟩
  exact ⟨l.l, l.fac_left, l.fac_right⟩

theorem abLocus_pullback (hA : AbLocusOneSt) {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G]
    (hG : IsSemiAbelian G) {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) (x : S') :
    f x ∈ abLocus G ↔ x ∈ abLocus G' := by
  have key : ∀ (K : Type) [Field K] (t : Sp K ⟶ S'),
      IsProper (pullback.snd G'.hom t) ↔ IsProper (pullback.snd G.hom (t ≫ f)) := by
    intro K _ t
    have hp := (IsPullback.of_hasPullback G'.hom t).paste_horiz h
    have e : pullback.snd G'.hom t = hp.isoPullback.hom ≫ pullback.snd G.hom (t ≫ f) :=
      hp.isoPullback_hom_snd.symm
    rw [e]
    constructor
    · intro hpr
      rw [← Iso.inv_hom_id_assoc hp.isoPullback (pullback.snd G.hom (t ≫ f))]
      infer_instance
    · intro hpr
      infer_instance
  constructor
  · intro hfx
    have hfx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), f x ∈ Set.range t →
        IsProper (pullback.snd G.hom t) := hfx
    intro K _ _ t hxt
    obtain ⟨p, hp⟩ := hxt
    exact (key K t).2 (hfx' K (t ≫ f) ⟨p, congrArg (fun y => f y) hp⟩)
  · intro hx
    have hx' : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S'), x ∈ Set.range t →
        IsProper (pullback.snd G'.hom t) := hx
    let κ := AlgebraicClosure (S'.residueField x)
    let t : Sp κ ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ)) ≫
      S'.fromSpecResidueField x
    have hxt : x ∈ Set.range t := by
      have hr := Scheme.range_fromSpecResidueField (X := S') x
      refine ⟨IsLocalRing.closedPoint κ, ?_⟩
      have hm : (S'.fromSpecResidueField x).base
          ((Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField x) κ))).base
            (IsLocalRing.closedPoint κ)) ∈ ({x} : Set S') := hr ▸ ⟨_, rfl⟩
      exact hm
    have hp := (key κ t).1 (hx' κ t hxt)
    obtain ⟨p, hp'⟩ := hxt
    exact hA S G hG κ (t ≫ f) hp ⟨p, congrArg (fun y => f y) hp'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem Model.j_s {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
