module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

open MeasureTheory

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6 Formalism.FourierDecayAlt.P.JCTx6.Pos

theorem posCoreQ : ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (χ : ℝ → ℝ) (A₀ ε : ℝ), C6.IsCut0 χ → 0 < ε →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ), (∀ i, d i ≠ 0) → t ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * As) f c →
      ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
        (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
          F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
        B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) (K * c) ∧
        (∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ)
          (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
          ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ) ∧
        ∀ γ ∈ B.GV k ρ, Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ) =>
          U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) z z' ξ •
            F (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) ξ (fun a => a.elim0) γ))
          (U.muXi k (ph + (n + 1)) 0 ρ (Dx2.SL.sigP σ)) :=
  posCoreQ_of Formalism.FourierDecayAlt.P.JCTx6.Int.intG Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable

end Formalism.FourierDecayAlt.P.PBE
