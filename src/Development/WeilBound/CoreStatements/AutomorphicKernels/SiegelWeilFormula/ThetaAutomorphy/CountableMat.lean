module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem countable_mat (p q : ℕ) : Countable (Matrix (Fin p) (Fin q) E) := by
  haveI := _root_.Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE (E := E)
  exact inferInstanceAs (Countable (Fin p → Fin q → E))

end PositivityTheory.SiegelWeilFormula.Tauto
