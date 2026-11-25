module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

@[expose] public section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section SlopeTestRemainingChoices

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_highest_weight_unit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsDS ε lam σ) : ∃ w : H, IsHighestUnit ε lam σ w := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · exact (le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS) :
      S ≤ lowKSub ε lam σ) (S.smul_mem _ hvS)
  · intro θ hθ
    rw [map_smul, hwt θ hθ, smul_comm]

end SlopeTestRemainingChoices

end Formalism.MainNotions.BridgeLemma
