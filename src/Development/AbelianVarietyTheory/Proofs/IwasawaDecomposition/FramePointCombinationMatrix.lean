module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.FramePairGram

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
  {t : SAB H X} {t' : SAB H X'} {S : Type} [CommRing S] {f : X' ⟶ X}

theorem left_pushE_symm_congr (m : SABMap t' t f) {q q' : Sp S ⟶ X'} (e : q = q') {x₀ x₀' : Sp S ⟶ X}
    (hq : q ≫ f = x₀) (hq' : q' ≫ f = x₀') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x₀ v)
    (hv' : IsTanAtG t x₀' v) :
    (tv ((pushE m q hq).symm (tanOf hv))).left = (tv ((pushE m q' hq').symm (tanOf hv'))).left := by
  subst e
  subst hq
  subst hq'
  rfl

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem ptF_eq_of_x_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x) :
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF y' :=
  pullback.hom_ext ((ptF_fst y).trans (h.trans (ptF_fst y').symm)) ((ptF_snd y).trans (ptF_snd y').symm)

theorem ofFrPt_v_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x)
    {x : Sp S ⟶ Z.X} (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (hv : IsTanAtG Xo.univ.t y'.x (y.u τ i)) :
    (EigFrame.ofFrPt Z y hx).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  show (tv (pushE Z.m (GlobalTheory.AllWt.ptF y) hx
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm (tanOf (t := Xo.univ.t) (y.tan τ i))))).left =
    (tv (pushE Z.m (GlobalTheory.AllWt.ptF y') hx'
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y') (ptF_fst y')).symm (tanOf hv)))).left
  rw [left_pushE, left_pushE,
    left_pushE_symm_congr Z.m0.toSABMap (ptF_eq_of_x_eq h) (ptF_fst y) (ptF_fst y') (y.tan τ i) hv]

theorem isComb_ofFrPt {S : Type} [CommRing S] [Algebra c.F S] (y' : FrPt Xo c S) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → S)
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAtG Xo.univ.t y'.x w)
    (hc : IsCombAtG Xo.univ.t y'.x (y'.u τ) a w) :
    IsCombAtG Z.t x' ((EigFrame.ofFrPt Z y' hx').v τ) a (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  have e := (isComb_iff (t := Xo.univ.t) (x := y'.x) (fun b => tanOf (t := Xo.univ.t) (y'.tan τ b)) a (tanOf hv)).1 hc
  refine (isComb_iff (t := Z.t) (x := x') (fun b => lieEquiv Z y' hx' (tanOf (t := Xo.univ.t) (y'.tan τ b))) a
    (lieEquiv Z y' hx' (tanOf hv))).2 ?_

  rw [e, map_sum]
  simp only [map_smul]

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

end Main

end GlobalTheory.FramePairGram
