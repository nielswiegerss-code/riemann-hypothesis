module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.GermExist

theorem isUnit_of_isSer1 (hrep : RepSt) (hser : SerSt) {R : Type} [CommRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {U : G.left.Opens} {f : Γ(G.left, U)} (hf : IsUnit f) {r : PS R 1 d} (h : IsSer1 x U f r) : IsUnit r := by
  obtain ⟨h1, -, h3, -⟩ := hrep R G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := h1 (pt R (n := 1) d 0) (gp_pt 0)
  have hc := (h3 _ y hy).1
  have hs := h 1 _ y hy
  have e : ev (n := 1) ![pt R (n := 1) d 0] r = r := by
    have : (![pt R d 0] : Fin 1 → Pt R 1 d) = fun j => pt R d j := by
      funext j; fin_cases j; rfl
    rw [this]
    unfold ev
    exact congrFun MvPowerSeries.subst_self r
  rw [e] at hs
  obtain ⟨⟨τ, hτ⟩, -⟩ := hser R (Fin 1 × Fin d) G.left (fun m => (y m).left)
    (fun m => by rw [← Over.comp_left, hc m]) U (hs 0).1
  rw [(hτ f r).1 hs]
  exact hf.map τ

theorem top_le_preimage_wchart {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : L.ι) (e : Z ⟶ Y) (h : ∀ k, ⊤ ≤ (e ≫ φ k) ⁻¹ᵁ L.U j) : ⊤ ≤ e ⁻¹ᵁ LB.wchart L φ (fun _ => j) := by
  intro z hz
  exact Set.mem_iInter.2 fun k => h k hz

theorem unit_comp_primφ {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by
  have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
    rw [MonObj.comp_one, Hom.one_def]
    simp
  have h2 : η[A] ≫ (𝟙 A * w : A ⟶ A) = η[A] := by
    rw [MonObj.comp_mul, hw, Category.comp_id]
    have : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by
      rw [Hom.one_def]; simp
    rw [this, _root_.mul_one]
  fin_cases k
  · exact Category.comp_id _
  · exact congrArg (·.left) h2
  · exact Category.comp_id _
  · exact congrArg (·.left) hw
  · exact congrArg (·.left) h1

end GlobalTheory.GermExist
