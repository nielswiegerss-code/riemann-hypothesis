module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Mathlib.Tactic.ENatToNat
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) = unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
