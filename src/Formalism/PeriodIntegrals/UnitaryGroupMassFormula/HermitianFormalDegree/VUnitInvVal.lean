module

public import Formalism.PeriodIntegrals.UpqRep
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal

namespace PI.UnitaryGroupMassFormula.FdegHpk

open PI.UpqRep

variable {n : ℕ}

theorem fdegOf_eq {ε : Fin n → Bool} (μ : Measure (UJ ε)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (w : H) (h : IsFdeg μ σ d) (hw : w ≠ 0) :
    fdegOf μ σ w = d := by
  unfold fdegOf
  obtain ⟨hd, hI⟩ := h
  obtain ⟨_, heq⟩ := hI w w w w
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have h1 : ∀ g : UJ ε, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    first
    | (rw [RCLike.star_def, RCLike.mul_conj]; push_cast; rfl)
  simp_rw [h1] at heq
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at heq
  have key : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d := by
    have h2 : ((‖w‖ : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (d : ℂ)) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      push_cast
      ring
    first
    | exact_mod_cast heq.trans h2
  rw [key]
  field_simp

end PI.UnitaryGroupMassFormula.FdegHpk
