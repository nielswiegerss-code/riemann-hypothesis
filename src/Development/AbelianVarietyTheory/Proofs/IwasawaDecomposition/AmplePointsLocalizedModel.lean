module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef.DomFine

theorem generalizing_of_stalk {Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : GeneralizingMap ξ := by
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by
    rw [Flat.SpecMap_iff]; exact hf
  have h₂ : GeneralizingMap (Y.fromSpecStalk (ξ (closedPoint _))) := by
    refine (Y.fromSpecStalk (ξ (closedPoint _))).isEmbedding.isInducing.generalizingMap ?_
    rw [Scheme.range_fromSpecStalk]
    exact fun a b hab hb => hab.trans hb
  have e : (ξ : Sp A → Y) = Y.fromSpecStalk (ξ (closedPoint _)) ∘ Spec.map (Scheme.stalkClosedPointTo ξ) := by
    funext p
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    exact Scheme.Hom.comp_apply _ _ _
  rw [e]
  exact (Flat.generalizingMap _).comp h₂

theorem eq_of_specializes {Y : Scheme.{0}} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) (w : Sp (FractionRing A)) (q : Y) (h : q ⤳ (jK A ≫ ξ) w) :
    q = (jK A ≫ ξ) w := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨r, hr, rfl⟩ := generalizing_of_stalk ξ hf h
  have hw : (jK A w).asIdeal = ⊥ := by
    haveI : (PrimeSpectrum.asIdeal w).IsPrime := PrimeSpectrum.isPrime w
    have hw₀ : PrimeSpectrum.asIdeal w = ⊥ := Ideal.eq_bot_of_prime _
    ext x
    change algebraMap A (FractionRing A) x ∈ PrimeSpectrum.asIdeal w ↔ _
    rw [hw₀, Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hle := (PrimeSpectrum.le_iff_specializes (R := A) r (jK A w)).mpr hr
  have : r = jK A w := by
    apply le_antisymm hle
    change (jK A w).asIdeal ≤ PrimeSpectrum.asIdeal r
    rw [hw]; exact bot_le
  rw [this]

theorem mem_range_of_generic {U V : Scheme.{0}} (j : U ⟶ V) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [TopologicalSpace.NoetherianSpace V] (g : V) (hg : ∀ q : V, q ⤳ g → q = g) : g ∈ Set.range j := by
  have hc : closure {g} ∈ irreducibleComponents V := by
    refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
    have hq := hS.isGenericPoint_genericPoint_closure
    have hgS : g ∈ S := hle (subset_closure rfl)
    have e := hg _ (hq.specializes (subset_closure hgS))
    rw [e] at hq
    exact subset_closure.trans hq.def.symm.subset
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨u, hu, hu'⟩ := hd.inter_open_nonempty o ho hne
  have hs : g ⤳ u := specializes_iff_mem_closure.2 (hle hu)
  exact j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hs hu'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem injective_of_flat {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat)
    (κ : O →+* A) (hκ : spMap κ = ξ₀ ≫ s) : Function.Injective ((algebraMap A (FractionRing A)).comp κ) := by
  have hsρ : spMap ((algebraMap A (FractionRing A)).comp κ) = (jK A ≫ ξ₀) ≫ s := by
    rw [← spMap_comp', hκ, Category.assoc]
  refine GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ (⊥ : PrimeSpectrum (FractionRing A)) ?_
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s
    (genericPoint_specializes (s ((jK A ≫ ξ₀) (⊥ : PrimeSpectrum (FractionRing A)))))
  have h := eq_of_specializes ξ₀ hfl (⊥ : PrimeSpectrum (FractionRing A)) y hy
  rw [hsρ]
  refine (Scheme.Hom.comp_apply (jK A ≫ ξ₀) s _).trans ?_
  rw [← h, e]

theorem exists_lift_frac {O F B : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F] [CommRing B]
    (g : O →+* B) (hu : ∀ y : O, y ≠ 0 → IsUnit (g y)) : ∃ ρ : F →+* B, ρ.comp (algebraMap O F) = g := by
  have hu' : ∀ y : nonZeroDivisors O, IsUnit (g y) := fun y => hu _ (nonZeroDivisors.ne_zero y.2)
  exact ⟨IsLocalization.lift hu', IsLocalization.lift_comp hu'⟩

theorem exists_generic_fibre {O F A : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X)
    (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ v : Sp (FractionRing A) ⟶ pullback s (spMap (algebraMap O F)), v ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ s)
  obtain ⟨κ, rfl⟩ : ∃ κ : O →+* A, CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ s := hκ'
  have hρ := injective_of_flat s hs ξ₀ hfl κ hκ
  obtain ⟨ρ', hρ'⟩ := exists_lift_frac (F := F) ((algebraMap A (FractionRing A)).comp κ) (fun y hy => by
    have h0 : κ y ≠ 0 := fun h => hy (hρ (by simp [h]))
    exact IsLocalization.map_units (FractionRing A) (⟨κ y, mem_nonZeroDivisors_of_ne_zero h0⟩ : nonZeroDivisors A))
  have hv : (jK A ≫ ξ₀) ≫ s = spMap ρ' ≫ spMap (algebraMap O F) := by
    rw [spMap_comp', hρ', ← spMap_comp', hκ, Category.assoc]
  exact ⟨pullback.lift (jK A ≫ ξ₀) _ hv, pullback.lift_fst _ _ _⟩

theorem exists_generic_point (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    (X U : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap (algebraMap O F))) (hs : Flat s) (hp : IsProjOver s)
    (hj : IsOpenImmersion jQ) (hd : Dense (Set.range jQ)) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ y : Sp (FractionRing A) ⟶ U, y ≫ jQ ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨v, v1⟩ := exists_generic_fibre (F := F) s hs ξ₀ hfl
  obtain ⟨hN, hC, -⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ hs hp hj hd
  haveI : IsNoetherian X := {}
  have hb0 : IsPreimmersion (spMap (algebraMap O F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  haveI h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb0
  haveI hNs : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap (algebraMap O F))) :=
    (pullback.fst s (spMap (algebraMap O F))).isEmbedding.isInducing.noetherianSpace
  have hr : Set.range v ⊆ Set.range jQ := by
    rintro _ ⟨w, rfl⟩
    refine mem_range_of_generic jQ hd _ fun q hq => ?_
    have h' := hq.map (pullback.fst s (spMap (algebraMap O F))).continuous
    have e : (pullback.fst s (spMap (algebraMap O F))) (v w) = (jK A ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, v1]
    rw [e] at h'
    exact (pullback.fst s (spMap (algebraMap O F))).isEmbedding.injective ((eq_of_specializes ξ₀ hfl w _ h').trans e.symm)
  refine ⟨IsOpenImmersion.lift jQ v hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, v1]

end GlobalTheory.TorRef.DomFine
