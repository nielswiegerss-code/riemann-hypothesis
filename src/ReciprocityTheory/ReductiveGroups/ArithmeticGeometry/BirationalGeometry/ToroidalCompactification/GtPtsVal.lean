module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

section Units

variable {Y Z W : Scheme.{0}}

theorem appTop_eq_of_gm (τ₁ τ₂ : Z ⟶ Y) (c₁ c₂ : Γ(Y, ⊤)ˣ) (h : ∀ z, gm τ₁ z ⊤ c₁ = gm τ₂ z ⊤ c₂) :
    τ₁.appTop.hom c₁.val = τ₂.appTop.hom c₂.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have h1 := congrArg Units.val (h z)
  unfold gm pullU at h1
  have m1 : τ₁ z ∈ (⊤ : Y.Opens) := trivial
  have m2 : τ₂ z ∈ (⊤ : Y.Opens) := trivial
  rw [dite_eq_left m1, dite_eq_left m2] at h1
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h1
  exact h1

theorem gm_comp_top (r : W ⟶ Z) (τ : Z ⟶ Y) (w : W) (c : Γ(Y, ⊤)ˣ) (c' : Γ(Z, ⊤)ˣ)
    (h : τ.appTop.hom c.val = c'.val) : gm (r ≫ τ) w ⊤ c = gm r w ⊤ c' := by
  apply Units.ext
  unfold gm pullU
  have m1 : (r ≫ τ) w ∈ (⊤ : Y.Opens) := trivial
  have m2 : r w ∈ (⊤ : Z.Opens) := trivial
  rw [dite_eq_left m1, dite_eq_left m2]
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.comp_app]
  rw [← h]
  rfl

theorem exists_ratio {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen)
    (ht' : t'.IsGen) : ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      val t r z J = gm r z ⊤ ρ * val t' r z J := by
  subst hφ
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL φ ε) t t' ht ht'
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  unfold val
  erw [hρ (fun k => J (r ≫ φ k)), map_mul]
  congr 1
  unfold gm res pullU
  have hm : r z ∈ L.wchart φ (fun k => J (r ≫ φ k)) := by
    unfold LB.wchart
    simp
    exact fun i => hJ (r ≫ φ i)
  rw [dite_eq_left hm, dite_eq_left (show r z ∈ (⊤ : Y.Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  try erw [Function.comp_apply]
  simp only [Units.coe_map]
  erw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply]
  erw [TopCat.Presheaf.germ_res_apply]

end Units

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

end Weight

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
