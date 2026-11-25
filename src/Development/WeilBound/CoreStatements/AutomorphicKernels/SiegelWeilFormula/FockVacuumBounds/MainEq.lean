module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

theorem iteratedDeriv_const_mul' (c : ℂ) (r : ℕ) : ∀ f : ℂ → ℂ,
    iteratedDeriv r (fun z => c * f z) = fun z => c * iteratedDeriv r f z :=
  fun f => funext fun _ => iteratedDeriv_const_mul_field c f

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Atop
