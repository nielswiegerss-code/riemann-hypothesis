module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.ContinuousSecondMatrix
public import Formalism.HermitianCurvature.StatementB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.OneLeGN

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec

open Formalism.QuantumDeterminants

theorem one_le_gN (k r : ℕ) (g : Mat k r) (hg : g ∈ UH (Hpk k r)) : 1 ≤ Formalism.FourierDecayAlt.B.gN g :=
  DecA.one_le_gN' hg

theorem of_cont (k r : ℕ) : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) :=
  continuous_matrix fun i j => by
    simp only [Matrix.of_apply]; exact (continuous_apply j).comp (continuous_apply i)

theorem gN_cont (k r : ℕ) : Continuous (fun M : Mat k r => Formalism.FourierDecayAlt.B.gN M) := by
  exact ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS.gN_continuous k r

theorem UW_inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hinv : h⁻¹ * h = 1 := DecA.inv_mul hU
  have key : ∀ v, h *ᵥ v = v → h⁻¹ *ᵥ v = v := fun v hv => by
    calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨DecA.inv_mem hU, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

theorem UH_closed (k r : ℕ) : IsClosed (UH (Hpk k r) : Set (Mat k r)) :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem UW_closed (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  exact Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z

theorem psiGen_cont (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun M : Mat k r => Formalism.MainNotions.S.psiGen k r z c M) := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.CurveContinuity.psiGen_cont <;> assumption

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Dec
