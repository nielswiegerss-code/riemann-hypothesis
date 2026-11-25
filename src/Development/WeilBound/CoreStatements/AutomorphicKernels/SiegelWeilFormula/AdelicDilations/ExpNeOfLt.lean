module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exp_ne_of_lt {m n : ℕ} (h : m < n) : Complex.exp ((2 * n - m : ℕ) : ℂ) ≠ Complex.exp (m : ℂ) := by
  intro e
  have e' : Real.exp ((2 * n - m : ℕ) : ℝ) = Real.exp (m : ℝ) := by
    have := congrArg Complex.re e
    rwa [← Complex.ofReal_natCast, ← Complex.ofReal_natCast (m : ℕ), Complex.exp_ofReal_re, Complex.exp_ofReal_re] at this
  have := Real.exp_injective e'
  have h2 : (2 * n - m : ℕ) = m := by exact_mod_cast this
  omega

end PositivityTheory.SiegelWeilFormula.AStep
