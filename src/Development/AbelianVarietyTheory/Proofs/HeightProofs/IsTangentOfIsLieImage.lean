module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LieLiftsTangentReduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero

@[expose] public section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  apply GlobalTheory.FormalValue.exists_isZero


variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)


omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}


end GlobalTheory.ArcLieCompare
