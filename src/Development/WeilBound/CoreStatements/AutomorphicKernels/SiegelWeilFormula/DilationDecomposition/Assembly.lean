module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.FirstCountableGR
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem iteratedDeriv_mul_const' (f : ℂ → ℂ) (c : ℂ) :
    ∀ r : ℕ, iteratedDeriv r (fun z => f z * c) = fun z => iteratedDeriv r f z * c :=
  fun _ => funext fun _ => iteratedDeriv_mul_const_field f c

end PositivityTheory.SiegelWeilFormula.Kdil
