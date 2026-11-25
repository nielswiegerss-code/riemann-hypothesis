module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfFacts

@[expose] public section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
  {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}

theorem discrete_series_isometry (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (v : H) :
    ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have := hDS.2.2.1.2.1 _ (cayley_conj_mem_diagonal_model hP ha).1 v
  simpa only [(cayley_conj_mem_diagonal_model hP ha).2] using this

theorem discrete_series_inner (hσ : IsDSHpk k r ε lam σ) {a : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (x y : H) :
    ⟪σ a x, σ a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ a : H →ₗ[ℂ] H) (discrete_series_isometry hσ ha)).inner_map_map x y

theorem discrete_series_continuousOn (hσ : IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have h1 := hDS.2.2.1.2.2 v
  have hc : Continuous fun x : Mat k r => P * x * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have h2 := h1.comp hc.continuousOn (fun a ha => (cayley_conj_mem_diagonal_model hP ha).1)
  refine h2.congr fun a ha => ?_
  simp only [Function.comp, (cayley_conj_mem_diagonal_model hP ha).2]

end Grp

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates
