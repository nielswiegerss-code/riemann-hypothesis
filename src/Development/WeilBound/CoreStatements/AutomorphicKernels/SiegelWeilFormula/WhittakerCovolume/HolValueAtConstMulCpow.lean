module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holValueAt_const_mul_cpow (c : ℂ) {C : ℝ} (hC : 0 < C) (s₀ : ℂ) :
    HolValueAt (fun z => c * (C : ℂ) ^ (z - s₀)) s₀ c := by
  have h := holValueAt_self (h := fun z => c * (C : ℂ) ^ (z - s₀)) (σ := s₀.re - 1) (s₀ := s₀)
    (fun z _ => analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const)
      (Complex.ofReal_mem_slitPlane.2 hC))) (by linarith)
  convert h using 1
  simp

end PositivityTheory.SiegelWeilFormula.KWhit
