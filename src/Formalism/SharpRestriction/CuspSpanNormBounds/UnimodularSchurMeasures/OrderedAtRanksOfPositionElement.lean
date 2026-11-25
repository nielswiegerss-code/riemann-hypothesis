module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

open scoped Matrix.Norms.Elementwise

theorem discrete_series_unitary_rep {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : CayleySignature.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    σ 1 = 1 ∧ (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      σ (x * y) = (σ x).comp (σ y)) ∧ ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, -, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hback : ∀ x : CayleySignature.Mat k r, P⁻¹ * (P * x * P⁻¹) * P = x := fun x => by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPi, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
    show (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) = Formalism.REAL.Jm ε
    have e1 : (P * x * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * x * P⁻¹) =
        (P⁻¹)ᴴ * (xᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * x) * P⁻¹ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e1, hPJ, hx', ← hPJ]
    calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hPi']; simp
  refine ⟨?_, fun x hx y hy => ?_, fun x hx v => ?_⟩
  · have : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hPi] at this
  · have := hmul _ (hmem x hx) _ (hmem y hy)
    simp only [hback] at this
    have e : P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = x * y := by
      calc P⁻¹ * (P * x * P⁻¹ * (P * y * P⁻¹)) * P = (P⁻¹ * P) * x * (P⁻¹ * P) * y * (P⁻¹ * P) := by
            simp only [Matrix.mul_assoc]
        _ = x * y := by rw [hPi]; simp
    rwa [e] at this
  · have := hiso _ (hmem x hx) v
    simp only [hback] at this
    exact this

section Pos

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (σ : CayleySignature.Mat k r → (H →L[ℂ] H))
  (hmul : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ (x * y) = (σ x).comp (σ y))
  (hone : σ 1 = 1)

include hmul in
theorem smooth_vectors_translate {ai : CayleySignature.Mat k r} (hai : ai ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) : σ ai v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨Uo, F, hO, hmem, hF, hEq⟩ := hv (g₀ * ai) (mat_mul_mem_UH_Hpk hg₀ hai)
  let L : CayleySignature.Mat k r →L[ℝ] CayleySignature.Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ ai)
  have hL : ∀ g, L g = g * ai := fun g => rfl
  refine ⟨L ⁻¹' Uo, fun g => F (L g), hO.preimage L.continuous, hmem, ?_, fun g hg hin => ?_⟩
  · exact hF.comp L.contDiff.contDiffOn (fun g hg => hg)
  · have h1 : σ (g * ai) v = F (g * ai) := hEq (g * ai) hg (mat_mul_mem_UH_Hpk hin hai)
    show σ g (σ ai v) = F (L g)
    rw [hL, ← h1, hmul g hin ai hai]; rfl


end Pos

end Formalism.MainNotions.LeviCoordinates
