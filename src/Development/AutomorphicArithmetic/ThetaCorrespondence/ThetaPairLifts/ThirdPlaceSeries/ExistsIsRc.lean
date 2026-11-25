module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain
namespace GlobalTheory.TypeRec.Model
open Classical in
theorem exists_isRc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) :
    ∃ rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc := by
  refine ⟨fun k v n π => if h : ∃ σ, Nonempty (π ≅ pull I k v σ) then
    (T.e _).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls h.choose))
    else D.naut.lpZero _, fun k v n σ π h => ?_⟩
  have h' : ∃ σ, Nonempty (π ≅ pull I k v σ) := ⟨σ, h⟩
  beta_reduce
  rw [dite_eq_left h', Equiv.apply_symm_apply, cls_eq_of_iso I k v _ σ ⟨h'.choose_spec.some.symm ≪≫ h.some⟩]
theorem locR_eq_rc_of_isRc_and_true_reading {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc}
    (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) {rep cp} (hc : IsComp I rep cp) {loc : D.what₂.FT → ∀ w, D.naut.LP w} {sat}
    (hr : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (loc σ w)) sat) (σ k v) :
    loc σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨s, hs, τ, h1, h2⟩ := hc σ k v
  apply (T.e _).injective
  rw [h2, h k v _ τ _ ⟨CategoryTheory.Iso.refl _⟩]
  have key : ∀ (w) (hs : s.w = w) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
      GlobalTheory.HeightCounting.IsLocS (rep σ).S s (hs ▸ τ) → T.e w (loc σ w) =
        _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) := by
    rintro _ rfl τ h1
    exact hr.1 σ s τ h1
  exact key _ hs τ h1
end GlobalTheory.TypeRec.Model
end
