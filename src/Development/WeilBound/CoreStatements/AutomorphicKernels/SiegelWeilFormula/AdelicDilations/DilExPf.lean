module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dilEx_pf (n : ℕ) (X : Fin n → ℝ) (τ : ℝ) : ∃ y : GR n, IsDil X τ y :=
  _root_.PositivityTheory.Rg.Sw.AbsSt.tsb_dil_exists n X τ

end PositivityTheory.SiegelWeilFormula.AStep
