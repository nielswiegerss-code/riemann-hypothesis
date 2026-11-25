module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Mathlib.Order.CompletePartialOrder
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Formalism.WachCohomologyFacts.PLenBound in
theorem submodule_generator_count : SubGen := by
  intro O _ _ _ M _ _ _ _ ℓ e F P h
  classical

  obtain ⟨k, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O M) F
  have hk : k ≤ Module.finrank O M := by
    have h1 := Submodule.finrank_le F
    rw [Module.finrank_eq_card_basis bF, Fintype.card_fin] at h1
    exact h1
  set Q := P.comap F.subtype with hQ
  let v : Fin k → ↥F ⧸ Q := fun i => Submodule.Quotient.mk (bF i)
  have hv_span : Submodule.span O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : (Submodule.Quotient.mk x : ↥F ⧸ Q) = ∑ i, bF.repr x i • v i := by
      conv_lhs => rw [← bF.sum_repr x]
      rw [← Submodule.mkQ_apply, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, v]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hv_kill : ∀ i, (ℓ ^ e) • v i = 0 := fun i => by
    dsimp only [v]
    rw [← Submodule.mkQ_apply, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hQ,
      Submodule.mem_comap, map_smul]
    exact h _ (bF i).2
  have hB := length_le_of_span v (ℓ ^ e) hv_span hv_kill
  rw [Fintype.card_fin] at hB
  calc Module.length O (↥F ⧸ Q)
      ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ ^ e}) := hB
    _ ≤ (k : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ})) := by
        gcongr
        exact length_quot_pow_le ℓ e
    _ ≤ ((Module.finrank O M * e : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
        push_cast
        rw [mul_assoc]
        gcongr

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
