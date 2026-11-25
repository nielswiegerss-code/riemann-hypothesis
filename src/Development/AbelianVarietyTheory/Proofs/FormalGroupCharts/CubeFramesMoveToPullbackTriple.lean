module

import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameDown

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

theorem frames_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e he
  have hφ : ∀ m, (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := by
    intro m
    funext J
    let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
      Over.homMk (𝟙 _) (by simp [overAt])
    have hj : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
      Over.OverMorphism.ext (by
        show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
          𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
        rw [Category.assoc, hx, Category.id_comp]
        rfl)
    refine (psum_push mp.cart _ ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U
      (fun i => ?_) J.down).trans (Category.id_comp _)
    fin_cases i
    · exact hj 0
    · exact hj 1
  choose c₁ hc₁ hcorr using fun m => ChartPrimTrPf.exists_reindex t.PP.L (hφ m) (cε 2) (e m) (he m)
  choose a ha hv using fun m => GlobalTheory.PrimDown.exists_down_all ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (c₁ m) (hc₁ m)
  exact ⟨a, ha, fun m => ⟨c₁ m, hcorr m, ChartPrimTrPf.maps_flat w _ _ (a m) (c₁ m) (hv m)⟩⟩

end GlobalTheory.FrameDown
