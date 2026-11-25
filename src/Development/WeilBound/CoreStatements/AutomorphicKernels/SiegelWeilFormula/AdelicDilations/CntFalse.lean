module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cnt_true (m : ℕ) : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

theorem cnt_false (m : ℕ) : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

end PositivityTheory.SiegelWeilFormula.AStep
