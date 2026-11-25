module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.LocalRingCardinality.DataLevel

@[expose] public section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

end Formalism.MainNotions.BridgeUnipRad
