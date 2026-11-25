module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentVecC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDerivAt0OfCart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.TrueCx.TorHolo GlobalTheory.TrueCx.TorFrHolo
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open Filter Topology
open scoped ContDiff CategoryTheory.Obj

namespace GlobalTheory.GramFamily

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

theorem isHolTo_cxPt {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  refine isHolTo_comp (isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_) Z.jQ
  simp only [ptC_fst]
  exact LocLift.isHolTo_congr h1 fun b _ => hx _

end Family

end GlobalTheory.GramFamily
