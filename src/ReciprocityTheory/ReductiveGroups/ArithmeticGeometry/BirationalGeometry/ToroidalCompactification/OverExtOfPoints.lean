module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem ext_of_schDom {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  have hΔ : IsClosedImmersion (pullback.diagonal s) := inferInstance
  have hi : IsClosedImmersion (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    inferInstance
  have hj : (ι ≫ f) ≫ pullback.diagonal s = ι ≫ pullback.lift f g h := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd, hU]
  have hji : pullback.lift (ι ≫ f) ι hj ≫ pullback.snd (pullback.diagonal s) (pullback.lift f g h) = ι :=
    pullback.lift_snd _ _ _
  have hker : (pullback.snd (pullback.diagonal s) (pullback.lift f g h)).ker = ⊥ := by
    apply le_bot_iff.mp
    have h0 := Scheme.Hom.le_ker_comp (pullback.lift (ι ≫ f) ι hj)
      (pullback.snd (pullback.diagonal s) (pullback.lift f g h))
    rw [hji, (inferInstance : IsSchemeTheoreticallyDominant ι).1] at h0
    exact h0
  have hiso : IsIso (pullback.snd (pullback.diagonal s) (pullback.lift f g h)) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.diagonal s) (g := pullback.lift f g h)
  have h1 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ f := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.fst s s) hc
  have h2 : pullback.fst (pullback.diagonal s) (pullback.lift f g h) =
      pullback.snd (pullback.diagonal s) (pullback.lift f g h) ≫ g := by
    simpa only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
      pullback.lift_fst, pullback.lift_snd] using congrArg (· ≫ pullback.snd s s) hc
  exact (cancel_epi _).mp (h1.symm.trans h2)

theorem schDom_spec_map {A B : Type} [CommRing A] [CommRing B] [IsReduced A] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := φ)).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]; exact bot_le)⟩
  exact IsSchemeTheoreticallyDominant.of_isDominant _




end ReciprocityTheory.ChartRestriction.G.Geo.Tor
