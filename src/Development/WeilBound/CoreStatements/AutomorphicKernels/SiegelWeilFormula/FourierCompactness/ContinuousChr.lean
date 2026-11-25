module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem continuous_chr {ψ : AddChar (AF F) ℂ} (hψ : Continuous ψ) {b : GL (Fin n ⊕ Fin n) E}
    (T : Matrix (Fin n) (Fin n) (AE F E)) :
    Continuous fun β : nA σ Y b => ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T * β.1)))) := by
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))
  exact hψ.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)

end PositivityTheory.SiegelWeilFormula.kfour
