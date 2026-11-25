module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroFormIntegrableCompact

@[expose] public section

open MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem opClos_le {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (l : Fin r)
    {B V : Submodule ℂ (RadSp k r z z' π π')} (hB : B ≤ V) (hV : ∀ (j : Fin 6), ∀ Φ ∈ V, X.op l j Φ ∈ V) :
    OpClos X l B ≤ V := by
  rw [OpClos, Submodule.span_le]
  rintro Φ ⟨js, Ψ, hΨ, rfl⟩
  show (js.map (X.op l)).prod Ψ ∈ V
  induction js with
  | nil => simpa using hB hΨ
  | cons j js ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact hV j _ ih

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem wave_operator_le_l2_subspace (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) :
    waveJ P z z' π π' D l ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Ψ hΨ => ?_
  obtain ⟨s, ε, G, Φ, Wv, -, hN, hlc, hΦ, hWv, rfl⟩ := unwave P z z' π π' D l Ψ hΨ
  refine unimodular_multiplier_preserves_L2 μ hμ hWv (fun _ _ => norm_fsv _ _) Φ ⟨hlc, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => G) (fun _ => G) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hN.2.1) (fun _ => hN.2.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  simpa [wt0] using h

end Wave

end Formalism.FourierDecayAlt.P.CutSE
