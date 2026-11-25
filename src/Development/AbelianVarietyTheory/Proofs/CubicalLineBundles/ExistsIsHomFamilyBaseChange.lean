module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G'] in
theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this


end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end PureType

end GlobalTheory
