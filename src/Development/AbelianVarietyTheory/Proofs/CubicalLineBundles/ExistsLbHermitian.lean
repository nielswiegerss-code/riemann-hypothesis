module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by

  simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

end GlobalTheory.HermTensorLB
