module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

@[expose] public section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem deltaEx' (h : IsCMExt F E σ) (ε : ℤˣ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -(((ε : ℤ) : E) * δ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨x, hx⟩ := _root_.GlobalTheory.AdelicU.exists_cm_conj_ne h
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, _root_.GlobalTheory.AdelicU.cm_conj_conj h]
    simp
  · exact ⟨1, one_ne_zero, by simp⟩

end PositivityTheory.SiegelWeilFormula.Act.CL
