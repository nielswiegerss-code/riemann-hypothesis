module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem real_indep {u v : ℂ} (hD : u.im * v.re - u.re * v.im ≠ 0) {x y : ℝ} (h : (x : ℂ) * u + (y : ℂ) * v = 0) :
    x = 0 ∧ y = 0 := by
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re, Complex.add_im, Complex.mul_im, add_zero, Complex.zero_im] at hr hi
  constructor
  · have e : x * (u.im * v.re - u.re * v.im) = 0 := by linear_combination v.re * hi - v.im * hr
    exact (mul_eq_zero.mp e).resolve_right hD
  · have e : y * (u.im * v.re - u.re * v.im) = 0 := by linear_combination u.im * hr - u.re * hi
    exact (mul_eq_zero.mp e).resolve_right hD

end PositivityTheory.SiegelWeilFormula.KFock
