module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.Move

variable {D : D7}

theorem heisO_eval_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : symplOH S T 0 w = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h]

theorem actO_one_left (V W : HSp D) (γ : GA D W) (w : WO V W) :
    actO V W 1 γ w = HMul.hMul (mt W γ) (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, _root_.GlobalTheory.BesselCompare.mt_one, Matrix.mul_one]

theorem om_rat_actO {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ) f (actO V W 1 γ w) = f w := by
  have h1 := H.om_heis 1 γ w f hf
  have h2 := H.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf w)
  rw [← heisO_eval_zero ψ V W (actO V W 1 γ w) (om (1, γ) f), ← h1, h2, heisO_eval_zero]

theorem om_rat_inv_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ⁻¹) f w = f (actO V W 1 γ w) := by
  have h := om_rat_actO H (inv_mem hγ) hf (actO V W 1 γ w)
  have e : actO V W 1 γ⁻¹ (actO V W 1 γ w) = w := by
    rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc, ← _root_.GlobalTheory.BesselCompare.mt_mul, inv_mul_cancel, _root_.GlobalTheory.BesselCompare.mt_one, Matrix.one_mul]
  rwa [e] at h

end GlobalTheory.RawLift.Move
